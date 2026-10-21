module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenBoundaryChart
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenOriginalRegion
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.HyperbolicConjugacy
public import LowDimensionalTopology.Geometry.Fuchsian.LimitSet.Approximation.HyperbolicLengthProperness
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.BoundaryHyperbolic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology MeasureTheory
open scoped UpperHalfPlane OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- A true complementary gap whose actual complete geodesic reaches a
positive-height bounded strip contains a uniformly long real interval in a
bounded enlargement of that strip. -/
theorem nielsenGap_strip_interval (G : Hyperbolic.NielsenHalfPlaneGap) (z : ℍ)
    (hz : z∈G.line.carrier) (ε : ℝ) (hε : 0<ε) (hy : ε≤z.im)
    (R : ℝ) (hR : |z.re|≤R) :
    ∃c : ℝ,Ioo c (c+ε)⊆G.carrier∩Ioo (-R-2*ε) (R+2*ε) := by
  obtain ⟨hxlo,hxhi⟩ := abs_le.mp hR
  cases G with
  | bounded a b hab =>
    have hnorm : ‖(z:ℂ)-(((a+b)/2:ℝ):ℂ)‖=(b-a)/2:=hz
    have hsq : (z.re-a)*(b-z.re)=z.im^2 := by
      have hh:=congrArg (fun x : ℝ=>x^2) hnorm
      rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply] at hh
      simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hh
      change (z.re-(a+b)/2)*(z.re-(a+b)/2)+z.im*z.im=((b-a)/2)^2 at hh
      nlinarith
    have hpos : 0<(z.re-a)*(b-z.re):=hsq ▸ sq_pos_of_pos z.im_pos
    have hx : a<z.re ∧ z.re<b := by
      rcases mul_pos_iff.mp hpos with ⟨ha,hb⟩|⟨ha,hb⟩ <;> constructor <;> linarith
    have hwide : ε≤z.re-a ∨ ε≤b-z.re := by
      by_contra hn
      push Not at hn
      have hh : 0<(ε-(z.re-a))*(ε-(b-z.re)):=mul_pos (by linarith [hn.1]) (by linarith [hn.2])
      nlinarith [sq_nonneg (z.im-ε)]
    rcases hwide with hleft|hright
    · refine ⟨z.re-ε,?_⟩
      intro t ht
      change t∈Ioo a b ∧ t∈Ioo (-R-2*ε) (R+2*ε)
      constructor <;> constructor <;> linarith [ht.1,ht.2,hx.1,hx.2]
    · refine ⟨z.re,?_⟩
      intro t ht
      change t∈Ioo a b ∧ t∈Ioo (-R-2*ε) (R+2*ε)
      constructor <;> constructor <;> linarith [ht.1,ht.2,hx.1,hx.2]
  | left b =>
    have hre : z.re=b:=hz
    refine ⟨b-ε,?_⟩
    intro t ht
    change t<b ∧ t∈Ioo (-R-2*ε) (R+2*ε)
    constructor
    · linarith [ht.2]
    · constructor <;> linarith [ht.1,ht.2]
  | right a =>
    have hre : z.re=a:=hz
    refine ⟨a,?_⟩
    intro t ht
    change a<t ∧ t∈Ioo (-R-2*ε) (R+2*ε)
    constructor
    · exact ht.1
    · constructor <;> linarith [ht.1,ht.2]

/-- The lower interval length gives a genuine uniform positive Lebesgue
measure bound on each actual gap meeting that native compact strip. -/
theorem nielsenGap_strip_measure_lower
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (z : ℍ)
    (hz : z∈G.line.carrier) (ε : ℝ) (hε : 0<ε) (hy : ε≤z.im)
    (R : ℝ) (hR : |z.re|≤R) :
    ENNReal.ofReal ε≤volume (G.carrier∩Ioo (-R-2*ε) (R+2*ε)) := by
  obtain ⟨c,hc⟩ := nielsenGap_strip_interval G z hz ε hε hy R hR
  have hh : volume (Ioo c (c+ε))≤volume (G.carrier∩Ioo (-R-2*ε) (R+2*ε)):=measure_mono hc
  rw [Real.volume_Ioo,show c+ε-c=ε by ring] at hh
  exact hh


/-- Distinct genuine complementary real gaps meeting one fixed bounded
positive-height strip form a finite set; the uniform measure bound is proved. -/
theorem nielsenRealGapFamily_strip_line_hits_finite (A : Set ℝ) (hA : IsClosed A)
    (ε : ℝ) (hε : 0<ε) (R : ℝ) :
    {S : Set ℝ | S∈Auxiliary.Topology.nielsenRealGapFamily A ∧ ∃G : Hyperbolic.NielsenHalfPlaneGap,
      G.carrier=S ∧ ∃z∈G.line.carrier,ε≤z.im ∧ |z.re|≤R}.Finite := by
  classical
  let ι:=Auxiliary.Topology.nielsenRealGapFamily A
  let B:=Ioo (-R-2*ε) (R+2*ε)
  let F (i : ι) : Set ℝ:=i.val∩B
  have hm (i : ι) : MeasurableSet (F i):=
    (Auxiliary.Topology.nielsenRealGapFamily_isOpen hA i.property).measurableSet.inter isOpen_Ioo.measurableSet
  have hd : Pairwise (fun i j : ι=>Disjoint (F i) (F j)) := by
    intro i j hij
    exact (Auxiliary.Topology.nielsenRealGapFamily_pairwiseDisjoint A i.property j.property
      (fun he=>hij (Subtype.ext he))).mono inter_subset_left inter_subset_left
  have hvol : volume (⋃i : ι,F i)≠⊤ := by
    apply ne_top_of_le_ne_top (b:=volume B)
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    · apply measure_mono
      exact iUnion_subset (fun _=>inter_subset_right)
  have hf:=Measure.finite_const_le_meas_of_disjoint_iUnion volume
    (ENNReal.ofReal_pos.mpr hε) hm hd hvol
  apply (hf.image (fun i : ι=>i.val)).subset
  rintro S ⟨hS,G,hGS,z,hz,hy,hre⟩
  refine ⟨⟨S,hS⟩,?_,rfl⟩
  change ENNReal.ofReal ε≤volume (S∩B)
  rw [←hGS]
  exact nielsenGap_strip_measure_lower G z hz ε hε hy R hre

/-- Genuine complete geodesics bounding different complementary real gaps
are locally finite in the actual half-plane. No boundary local-finiteness
or finite-polygon hypothesis is assumed. -/
theorem nielsenRealGapFamily_compact_line_hits_finite (A : Set ℝ) (hA : IsClosed A)
    (K : Set ℍ) (hK : IsCompact K) :
    {S : Set ℝ | S∈Auxiliary.Topology.nielsenRealGapFamily A ∧ ∃G : Hyperbolic.NielsenHalfPlaneGap,
      G.carrier=S ∧ (G.line.carrier∩K).Nonempty}.Finite := by
  rcases K.eq_empty_or_nonempty with rfl|hne
  · simp
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨R,hR⟩ := (hK.image UpperHalfPlane.continuous_re).isBounded.subset_closedBall (0:ℝ)
  apply (nielsenRealGapFamily_strip_line_hits_finite A hA z.im z.im_pos R).subset
  rintro S ⟨hS,G,hGS,w,hwG,hwK⟩
  refine ⟨hS,G,hGS,w,hwG,hmin hwK,?_⟩
  have hh:=hR (mem_image_of_mem UpperHalfPlane.re hwK)
  simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hh


/-- If the real boundary trace has no actual spherical accumulation at
infinity, its real coordinates are genuinely uniformly bounded. -/
theorem nielsenRealBoundary_bounded_of_infty_not_closure (S : Set ℝ)
    (h : (∞:OnePoint ℂ)∉closure (Hyperbolic.nielsenRealBoundaryPoint '' S)) :
    ∃R : ℝ,∀x∈S,|x|≤R := by
  let C:=closure (Hyperbolic.nielsenRealBoundaryPoint '' S)
  have hC : IsCompact C:=isClosed_closure.isCompact
  have hfinite : C⊆range ((↑) : ℂ→OnePoint ℂ) := by
    intro p hp
    cases p with
    | infty => exact False.elim (h hp)
    | coe z => exact ⟨z,rfl⟩
  have hK : IsCompact (((↑) : ℂ→OnePoint ℂ) ⁻¹' C):=
    (OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage_iff hfinite).mpr hC
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0:ℂ)
  refine ⟨R,?_⟩
  intro x hx
  have hxK : (x:ℂ)∈((↑) : ℂ→OnePoint ℂ) ⁻¹' C:=subset_closure (mem_image_of_mem Hyperbolic.nielsenRealBoundaryPoint hx)
  have hh:=hR hxK
  simpa only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs] using hh

/-- Both actual unbounded real half-rays accumulate at the true spherical
point at infinity. -/
theorem nielsenRealBoundary_infty_mem_half_ray_closures (b : ℝ) :
    (∞:OnePoint ℂ)∈closure (Hyperbolic.nielsenRealBoundaryPoint '' Iio b) ∧
    (∞:OnePoint ℂ)∈closure (Hyperbolic.nielsenRealBoundaryPoint '' Ioi b) := by
  constructor
  · by_contra hn
    obtain ⟨R,hR⟩ := nielsenRealBoundary_bounded_of_infty_not_closure (Iio b) hn
    have hh:=hR (min b (-R)-1) (by change min b (-R)-1<b;linarith [min_le_left b (-R)])
    linarith [min_le_right b (-R),neg_le_abs (min b (-R)-1)]
  · by_contra hn
    obtain ⟨R,hR⟩ := nielsenRealBoundary_bounded_of_infty_not_closure (Ioi b) hn
    have hh:=hR (max b R+1) (by change b<max b R+1;linarith [le_max_left b R])
    linarith [le_max_right b R,le_abs_self (max b R+1)]

/-- Every actual gap-line endpoint is a genuine spherical limit point of
the corresponding real boundary interval but is not in the open interval. -/
theorem nielsenGap_idealEndpoints_subset_interval_frontier
    (G : Hyperbolic.NielsenHalfPlaneGap) :
    G.line.idealEndpoints⊆closure (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)\
      (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier) := by
  have hfinite (S : Set ℝ) (x : ℝ) (hx : x∈closure S) (hn : x∉S) :
      Hyperbolic.nielsenRealBoundaryPoint x∈closure (Hyperbolic.nielsenRealBoundaryPoint '' S)\(Hyperbolic.nielsenRealBoundaryPoint '' S) := by
    refine ⟨image_closure_subset_closure_image Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.continuous
      (mem_image_of_mem Hyperbolic.nielsenRealBoundaryPoint hx),?_⟩
    rwa [Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.injective.mem_set_image]
  cases G with
  | bounded a b hab =>
    rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
    apply pair_subset
    · exact hfinite (Ioo a b) a (by rw [closure_Ioo hab.ne];exact ⟨le_rfl,hab.le⟩) (by simp)
    · exact hfinite (Ioo a b) b (by rw [closure_Ioo hab.ne];exact ⟨hab.le,le_rfl⟩) (by simp)
  | left b =>
    rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
    apply pair_subset
    · exact hfinite (Iio b) b (by rw [closure_Iio];exact le_rfl) (by simp)
    · exact ⟨(nielsenRealBoundary_infty_mem_half_ray_closures b).1,by rintro ⟨x,_hx,hx⟩;exact (OnePoint.coe_ne_infty (x:ℂ)) hx⟩
  | right a =>
    rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
    apply pair_subset
    · exact hfinite (Ioi a) a (by rw [closure_Ioi];exact le_rfl) (by simp)
    · exact ⟨(nielsenRealBoundary_infty_mem_half_ray_closures a).2,by rintro ⟨x,_hx,hx⟩;exact (OnePoint.coe_ne_infty (x:ℂ)) hx⟩


/-- The two actual ideal endpoints are exactly the spherical endpoints of
an actual open real gap, including infinity for either unbounded gap. -/
theorem nielsenGap_interval_endpoints (G : Hyperbolic.NielsenHalfPlaneGap) :
    closure (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)\(Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)=
      G.line.idealEndpoints := by
  apply subset_antisymm _ (nielsenGap_idealEndpoints_subset_interval_frontier G)
  rintro p ⟨hp,hnot⟩
  have hB : closure (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)⊆Hyperbolic.halfPlaneIdealBoundary := by
    apply closure_minimal
    · rintro _ ⟨x,_hx,rfl⟩
      exact (Hyperbolic.coe_mem_halfPlaneIdealBoundary (x:ℂ)).mpr (by simp)
    · rw [←nielsen_openHalfPlane_frontier]
      exact isClosed_frontier
  cases p with
  | infty =>
    cases G with
    | bounded a b hab =>
      have hc : IsCompact (Hyperbolic.nielsenRealBoundaryPoint '' Icc a b):=
        isCompact_Icc.image Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.continuous
      have hs : closure (Hyperbolic.nielsenRealBoundaryPoint '' Ioo a
        b)⊆Hyperbolic.nielsenRealBoundaryPoint '' Icc a b:=
        closure_minimal (image_mono Ioo_subset_Icc_self) hc.isClosed
      obtain ⟨x,_hx,hx⟩ := hs hp
      exact False.elim ((OnePoint.coe_ne_infty (x:ℂ)) hx)
    | left b => rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact mem_insert_of_mem _ (mem_singleton ∞)
    | right a => rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints];exact mem_insert_of_mem _ (mem_singleton ∞)
  | coe z =>
    have him : z.im=0:=(Hyperbolic.coe_mem_halfPlaneIdealBoundary z).mp (hB hp)
    let x:=z.re
    have hzx : z=(x:ℂ):=Complex.ext rfl him
    have hxcl : x∈closure G.carrier := by
      rw [Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.closure_eq_preimage_closure_image]
      change Hyperbolic.nielsenRealBoundaryPoint x∈closure (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)
      simpa only [Hyperbolic.nielsenRealBoundaryPoint,hzx] using hp
    have hxnot : x∉G.carrier := by
      intro hx
      exact hnot ⟨x,hx,congrArg OnePoint.some hzx.symm⟩
    cases G with
    | bounded a b hab =>
      change x∈closure (Ioo a b) at hxcl
      change x∉Ioo a b at hxnot
      rw [closure_Ioo hab.ne] at hxcl
      have heq : x=a ∨ x=b := by
        simp only [mem_Icc] at hxcl
        simp only [mem_Ioo,not_and_or,not_lt] at hxnot
        rcases hxnot with h|h
        · exact Or.inl (by linarith [hxcl.1])
        · exact Or.inr (by linarith [hxcl.2])
      rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints,hzx]
      rcases heq with rfl|rfl
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_singleton _)
    | left b =>
      change x∈closure (Iio b) at hxcl
      change x∉Iio b at hxnot
      rw [closure_Iio] at hxcl
      have heq : x=b:=by simpa only [mem_Iic,mem_Iio,not_lt] using le_antisymm hxcl (not_lt.mp hxnot)
      rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints,hzx,heq]
      exact mem_insert _ _
    | right a =>
      change x∈closure (Ioi a) at hxcl
      change x∉Ioi a at hxnot
      rw [closure_Ioi] at hxcl
      have heq : x=a:=le_antisymm (not_lt.mp hxnot) hxcl
      rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints,hzx,heq]
      exact mem_insert _ _


/-- A genuine hyperbolic real Mobius transformation preserving an actual
complementary interval has precisely that interval's complete geodesic as
its true metric axis. Endpoint preservation is proved from the interval. -/
theorem nielsenGap_axis_of_hyperbolic_interval_preservation
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2)
    (hI : (Hyperbolic.realSLMobius A).val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)=
      Hyperbolic.nielsenRealBoundaryPoint '' G.carrier) : G.line=Hyperbolic.hHyperbolicAxis A hA ht := by
  have hAH : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius A):=(Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr ht
  have hend : (Hyperbolic.realSLMobius A).val '' G.line.idealEndpoints=G.line.idealEndpoints := by
    rw [←nielsenGap_interval_endpoints,image_sdiff (Hyperbolic.realSLMobius A).val.injective]
    change (Mobius.mobiusBoundaryHomeomorph (Hyperbolic.realSLMobius A)) '' closure (Hyperbolic.nielsenRealBoundaryPoint
      '' G.carrier)\
      (Hyperbolic.realSLMobius A).val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)=_
    rw [Homeomorph.image_closure,hI]
    change closure ((Hyperbolic.realSLMobius A).val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier))\
      (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)=_
    rw [hI]
  obtain ⟨a,b,_γ,hab,_haB,_hbB,hpair,_hγ,_hrange,_hlim,_hlim'⟩ := G.line.exists_idealEndpoints_pair
  have hFa : (Hyperbolic.realSLMobius A).val a=a ∨ (Hyperbolic.realSLMobius A).val a=b := by
    have hh:=mem_image_of_mem (Hyperbolic.realSLMobius A).val (hpair.symm ▸ mem_insert a {b})
    rw [hend,hpair] at hh
    exact hh
  have hFb : (Hyperbolic.realSLMobius A).val b=a ∨ (Hyperbolic.realSLMobius A).val b=b := by
    have hh:=mem_image_of_mem (Hyperbolic.realSLMobius A).val (hpair.symm ▸ mem_insert_of_mem a (mem_singleton b))
    rw [hend,hpair] at hh
    exact hh
  have hfixed : (Hyperbolic.realSLMobius A).val a=a ∧ (Hyperbolic.realSLMobius A).val b=b := by
    rcases hFa with hFa|hFa
    · refine ⟨hFa,?_⟩
      exact hFb.resolve_left (fun hb=>hab ((Hyperbolic.realSLMobius A).val.injective (hFa.trans hb.symm)))
    · have hb : (Hyperbolic.realSLMobius A).val b=a :=
        hFb.resolve_right (fun hb=>hab ((Hyperbolic.realSLMobius A).val.injective (hFa.trans hb.symm)))
      have hs:=Mobius.mobius_sq_eq_one_of_swaps (Hyperbolic.realSLMobius A) a b hab hFa hb
      exact False.elim (hAH.1.not_elliptic (Mobius.mobius_finite_order_elliptic _ hA
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hs⟩)))
  apply Hyperbolic.hHyperbolicAxis_unique A hA ht
  obtain ⟨c,d,hcd,hfix⟩ := DiscreteGroups.mobius_loxodromic_boundary_fixed_pair (Hyperbolic.realSLMobius A) hAH.1
  have hac:=(hfix a).mp hfixed.1
  have hbc:=(hfix b).mp hfixed.2
  have heq : ({a,b}:Set (OnePoint ℂ))={c,d} := by
    rcases hac with rfl|rfl <;> rcases hbc with rfl|rfl
    · exact False.elim (hab rfl)
    · rfl
    · exact pair_comm _ _
    · exact False.elim (hab rfl)
  rw [hpair,heq]
  ext z
  exact (hfix z).symm


/-- Equality of the genuine complementary real intervals determines their
complete hyperbolic boundary geodesic exactly. -/
theorem nielsenGap_line_eq_of_carrier_eq (G J : Hyperbolic.NielsenHalfPlaneGap)
    (h : G.carrier=J.carrier) : G.line=J.line := by
  apply Hyperbolic.HalfPlaneLine.idealEndpoints_injective
  rw [←nielsenGap_interval_endpoints,←nielsenGap_interval_endpoints,h]


/-- An actual minimizing displacement point lies on the genuine hyperbolic
axis in every original-group half-plane coordinate. -/
theorem normalized_hyperbolic_minimum_axis_membership
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (q : Mobius.complexMobiusGroup) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : Hyperbolic.realSLMobius B=q*Hyperbolic.cayleyMobius) (f : H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A=q*f.val*q⁻¹)
    (hAn : Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2)
    (u : 𝔻) (hmin : Hyperbolic.discPathDist u (P.discAction f u)=Hyperbolic.dTranslationLength (P.discAction f)) :
    B • Hyperbolic.discToHalfPlane u∈(Hyperbolic.hHyperbolicAxis A hAn ht).carrier := by
  have hact (z : 𝔻) : A • (B • Hyperbolic.discToHalfPlane z)=B • Hyperbolic.discToHalfPlane (P.discAction f z) := by
    have hh:=normalizedPolygonHalfPlaneChart_smul P q B hB f A hA (P.finiteCoordinate.symm z)
    change A • (B • Hyperbolic.discToHalfPlane (P.finiteCoordinate (P.finiteCoordinate.symm z)))=
      B • Hyperbolic.discToHalfPlane (P.discAction f z) at hh
    simpa only [P.finiteCoordinate.apply_symm_apply] using hh
  have hd (z : 𝔻) : dist (B • Hyperbolic.discToHalfPlane z) (A • (B • Hyperbolic.discToHalfPlane z))=
      Hyperbolic.discPathDist z (P.discAction f z) := by
    rw [hact,(isometry_smul ℍ B).dist_eq]
    exact (Hyperbolic.discPathDist_eq_halfPlane z (P.discAction f z)).symm
  have hT : Hyperbolic.hTranslationLength (Hyperbolic.hSLIsometry A)=Hyperbolic.dTranslationLength (P.discAction f) := by
    change sInf (range (fun w : ℍ=>dist w (A • w)))=
      sInf (range (fun z : 𝔻=>Hyperbolic.discPathDist z (P.discAction f z)))
    congr 1
    ext r
    constructor
    · rintro ⟨w,rfl⟩
      refine ⟨Hyperbolic.halfPlaneToDisc (B⁻¹ • w),?_⟩
      change Hyperbolic.discPathDist (Hyperbolic.halfPlaneToDisc (B⁻¹ • w)) (P.discAction f (Hyperbolic.halfPlaneToDisc
        (B⁻¹ • w)))=dist w (A • w)
      rw [←hd,Hyperbolic.discToHalfPlane_halfPlaneToDisc,smul_inv_smul]
    · rintro ⟨z,rfl⟩
      exact ⟨B • Hyperbolic.discToHalfPlane z,hd z⟩
  apply (Hyperbolic.hHyperbolic_translation_minimum A hAn ht _).mp
  rw [hd,hT]
  exact hmin


/-- In every genuine whole-group half-plane chart, one actual compact set
meets an axis representative from each true hyperbolic conjugacy class. -/
theorem finitelyGenerated_normalized_axis_compact_core
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG)
    (q : Mobius.complexMobiusGroup) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : Hyperbolic.realSLMobius B=q*Hyperbolic.cayleyMobius) :
    ∃K : Set ℍ,IsCompact K ∧ ∀f : H,Mobius.MobiusHyperbolic f.val→
      ∃g : H,∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        Hyperbolic.realSLMobius A=q*(g⁻¹*f*g).val*q⁻¹ ∧
        ∀(hAn : Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2),
          ((Hyperbolic.hHyperbolicAxis A hAn ht).carrier∩K).Nonempty := by
  obtain ⟨K,hK,hMin⟩ := finitelyGenerated_uniform_axis_minimum_core P hFG
  let F : 𝔻→ℍ:=fun z=>B • Hyperbolic.discToHalfPlane z
  have hF : Continuous F:=(isometry_smul ℍ B).continuous.comp Hyperbolic.cayleyHomeomorph.symm.continuous
  refine ⟨F '' K,hK.image hF,?_⟩
  intro f hf
  obtain ⟨g,u,hu,hmin⟩ := hMin f hf
  let k : H:=g⁻¹*f*g
  obtain ⟨A₀,hA₀,_hact⟩ := fuchsian_disc_real_lift P k
  let A:=B*A₀*B⁻¹
  have hA : Hyperbolic.realSLMobius A=q*k.val*q⁻¹ := by
    change Hyperbolic.realSLMobius (B*A₀*B⁻¹)=_
    rw [map_mul,map_mul,map_inv,hB,hA₀]
    group
  refine ⟨g,A,hA,?_⟩
  intro hAn ht
  have hmin' : Hyperbolic.discPathDist u (P.discAction k u)=Hyperbolic.dTranslationLength (P.discAction k):=
    hmin.trans (fuchsian_disc_translationLength_conjugation P f g).symm
  exact ⟨F u,normalized_hyperbolic_minimum_axis_membership P q B hB k A hA hAn ht u hmin',⟨u,hu,rfl⟩⟩

/-- A genuine maximal cyclic subgroup is the full actual point stabilizer
at every fixed point of any one of its nonidentity members. -/
theorem maximalCyclic_eq_boundaryStabilizer_of_fixed
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (K : Subgroup Mobius.complexMobiusGroup) (hK : IsMaximalCyclicIn H K)
    (f : Mobius.complexMobiusGroup) (hfK : f∈K) (hfn : f≠1)
    (ξ : Mobius.ExtendedComplex)
    (hfix : f.val ξ=ξ) : K=DiscreteGroups.mobiusBoundaryStabilizer H ξ := by
  have hKS : K≤DiscreteGroups.mobiusBoundaryStabilizer H ξ := by
    intro g hg
    exact (DiscreteGroups.mem_mobiusBoundaryStabilizer H ξ g).mpr ⟨hK.1 hg,
      cyclic_mobius_fixedPoint K hK.2.1 f hfK hfn ξ hfix g hg⟩
  exact (hK.2.2 (DiscreteGroups.mobiusBoundaryStabilizer H ξ)
    (fun g hg=>((DiscreteGroups.mem_mobiusBoundaryStabilizer H ξ g).mp hg).1)
    (D.stabilizer_isCyclic ξ) hKS).symm


/-- Actual conjugacy inside the original group transports its full true
point stabilizers, without replacing the ambient group. -/
theorem boundaryStabilizer_inner_conjugation
    {H : Subgroup Mobius.complexMobiusGroup}
    (g : H)
    (p : Mobius.ExtendedComplex) :
    DiscreteGroups.Action.Actions.subgroupConjugate g.val (DiscreteGroups.mobiusBoundaryStabilizer H p)=
      DiscreteGroups.mobiusBoundaryStabilizer H (g.val.val p) := by
  have hH : DiscreteGroups.Action.Actions.subgroupConjugate g.val H=H := by
    ext f
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact H.mul_mem (H.mul_mem g.property hk) (H.inv_mem g.property)
    · intro hf
      refine ⟨g.val⁻¹*f*g.val,H.mul_mem (H.mul_mem (H.inv_mem g.property) hf) g.property,?_⟩
      change g.val*(g.val⁻¹*f*g.val)*g.val⁻¹=f
      group
  rw [←primitive_boundaryStabilizer_conjugation,hH]

/-- Every genuine boundary hyperbolic interval becomes a true complementary
real gap in an actual Nielsen chart, and its actual axis is the gap line. -/
theorem boundaryHyperbolic_normalized_gap
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hinf : (∞:OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H))
    (f : H) (hf : IsBoundaryHyperbolic D f)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Hyperbolic.realSLMobius A=q*f.val*q⁻¹)
    (hAn : Hyperbolic.realSLMobius A≠1) (ht : 4<(Matrix.trace A.val)^2) :
    ∃G : Hyperbolic.NielsenHalfPlaneGap,
      G.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet
        (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H))) ∧
      G.line=Hyperbolic.hHyperbolicAxis A hAn ht := by
  obtain ⟨I,hI,hfI⟩ := hf.2
  have hIF : I∈D.nielsenArcFamily := by
    obtain ⟨p,hp,hIp⟩ := hI.1
    refine ⟨p,?_,?_⟩
    · rw [←fuchsianLimitSet_eq_nonElementary H hNE]
      exact hp
    · change I=connectedComponentIn (frontier D.carrier\DiscreteGroups.mobiusLimitSet H) p
      rw [←fuchsianLimitSet_eq_nonElementary H hNE]
      exact hIp
  obtain ⟨G,hGI⟩ := D.nielsenArcFamily_exists_gap q hq hNE hinf hIF
  have hGF : Hyperbolic.nielsenRealBoundaryPoint '' G.carrier∈
      Hyperbolic.nielsenHalfPlaneArcFamily (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)) := by
    apply (D.nielsenArcFamily_gap_mem q hq G).mp
    rw [hGI]
    exact hIF
  rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf] at hGF
  obtain ⟨S,hS,hSG⟩ := hGF
  have hGS : S=G.carrier:=Hyperbolic.nielsenRealBoundaryPoint_isEmbedding.injective.image_injective hSG
  have hqI : q.val '' I=Hyperbolic.nielsenRealBoundaryPoint '' G.carrier := by
    rw [←hGI]
    exact q.val.image_symm_image _
  have hpres : (Hyperbolic.realSLMobius A).val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier)=
      Hyperbolic.nielsenRealBoundaryPoint '' G.carrier := by
    rw [hA]
    calc
      _=q.val '' (f.val.val '' (q⁻¹.val '' (Hyperbolic.nielsenRealBoundaryPoint '' G.carrier))) := by
        simp only [image_image]
        rfl
      _=Hyperbolic.nielsenRealBoundaryPoint '' G.carrier := by rw [hGI,hfI,hqI]
  exact ⟨G,hGS ▸ hS,nielsenGap_axis_of_hyperbolic_interval_preservation G A hAn ht hpres⟩


/-- Finite generation gives a genuine finite set of actual subgroup
conjugacy representatives for all maximal boundary-hyperbolic cyclic
subgroups. The original non-elementary case is proved through actual gaps. -/
theorem finitelyGenerated_nonElementary_boundary_cyclic_representatives
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG) :
    ∃E : Finset (Subgroup Mobius.complexMobiusGroup),∀K : Subgroup Mobius.complexMobiusGroup,
      IsMaximalCyclicIn H K→∀f : H,f.val∈K→IsBoundaryHyperbolic P.asFuchsianDisc f→
      ∃g : H,DiscreteGroups.Action.Actions.subgroupConjugate g.val K∈E := by
  classical
  let D:=P.asFuchsianDisc
  let q:=D.nielsenArcNormalizer hNE
  have hq:=D.nielsenArcNormalizer_image hNE
  have hinf:=D.nielsenArcNormalizer_limit hNE
  have hpres : (q*Hyperbolic.cayleyMobius).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
    change (fun z=>q.val (Hyperbolic.cayleyMobius.val z)) '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet
    rw [←image_image,cayleyMobius_image_openHalfPlane]
    exact hq
  obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
  obtain ⟨K₀,hK₀,hCore⟩ := finitelyGenerated_normalized_axis_compact_core P hFG q B hB
  let A₀:=Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet
    (DiscreteGroups.Action.Actions.subgroupConjugate q H))
  have hA₀ : IsClosed A₀:=Hyperbolic.nielsenHalfPlaneRealSet_isClosed _ (DiscreteGroups.mobiusLimitSet_isClosed _)
  let S₀ : Set (Set ℝ):={S | S∈Auxiliary.Topology.nielsenRealGapFamily A₀ ∧ ∃G : Hyperbolic.NielsenHalfPlaneGap,
    G.carrier=S ∧ (G.line.carrier∩K₀).Nonempty}
  have hS₀ : S₀.Finite:=nielsenRealGapFamily_compact_line_hits_finite A₀ hA₀ K₀ hK₀
  let ι:=S₀
  have : Finite ι:=hS₀.to_subtype
  have hGs (i : ι) : ∃G : Hyperbolic.NielsenHalfPlaneGap,G.carrier=i.val ∧ (G.line.carrier∩K₀).Nonempty:=i.property.2
  choose Gs hGS _hGhit using hGs
  have hend (i : ι) : ∃a : OnePoint ℂ,a∈(Gs i).line.idealEndpoints := by
    obtain ⟨a,b,_γ,_hab,_ha,_hb,he,_hγ,_hrange,_hlim,_hlim'⟩ := (Gs i).line.exists_idealEndpoints_pair
    exact ⟨a,he.symm ▸ mem_insert a {b}⟩
  choose a ha using hend
  let F (i : ι) : Subgroup Mobius.complexMobiusGroup:=DiscreteGroups.mobiusBoundaryStabilizer H (q.val.symm (a i))
  have hF : (range F).Finite:=Set.finite_range F
  refine ⟨hF.toFinset,?_⟩
  intro K hK f hfK hf
  obtain ⟨g,A,hA,haxis⟩ := hCore f hf.1
  let k : H:=g⁻¹*f*g
  have hkb : IsBoundaryHyperbolic D k := by
    simpa only [inv_inv] using hf.conjugate g⁻¹
  have hAH : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius A) := by
    rw [hA]
    exact Mobius.mobiusHyperbolic_conjugation_forward k.val q hkb.1
  have hAn : Hyperbolic.realSLMobius A≠1:=hAH.1.1
  have ht:=(Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp hAH
  obtain ⟨G,hGF,hGL⟩ := boundaryHyperbolic_normalized_gap D hNE q hq hinf k hkb A hA hAn ht
  obtain ⟨z,hzA,hzK⟩ := haxis hAn ht
  have hzG : z∈G.line.carrier:=hGL.symm ▸ hzA
  let i : ι:=⟨G.carrier,hGF,G,rfl,z,hzG,hzK⟩
  have hGline : (Gs i).line=G.line:=nielsenGap_line_eq_of_carrier_eq _ _ (hGS i)
  have hpoint : a i∈(Hyperbolic.hHyperbolicAxis A hAn ht).idealEndpoints := by
    rw [←hGL,←hGline]
    exact ha i
  have hAfixed : (Hyperbolic.realSLMobius A).val (a i)=a i := by
    rwa [Hyperbolic.hHyperbolicAxis_idealEndpoints] at hpoint
  let ξ:=q.val.symm (a i)
  have hkfixed : k.val.val ξ=ξ := by
    apply q.val.injective
    rw [hA] at hAfixed
    change q.val (k.val.val (q.val.symm (a i)))=a i at hAfixed
    change q.val (k.val.val (q.val.symm (a i)))=q.val (q.val.symm (a i))
    rwa [q.val.apply_symm_apply]
  have hffixed : f.val.val (g.val.val ξ)=g.val.val ξ := by
    have hh:=congrArg g.val.val hkfixed
    change g.val.val (g.val.val.symm (f.val.val (g.val.val ξ)))=g.val.val ξ at hh
    simpa only [g.val.val.apply_symm_apply] using hh
  have hKS : K=DiscreteGroups.mobiusBoundaryStabilizer H (g.val.val ξ):=
    maximalCyclic_eq_boundaryStabilizer_of_fixed D K hK f.val hfK hf.1.1.1 _ hffixed
  refine ⟨g⁻¹,hF.mem_toFinset.mpr ?_⟩
  have hconj : DiscreteGroups.Action.Actions.subgroupConjugate (g⁻¹).val K=F i := by
    rw [hKS,boundaryStabilizer_inner_conjugation]
    change DiscreteGroups.mobiusBoundaryStabilizer H (g.val.val.symm (g.val.val
      ξ))=DiscreteGroups.mobiusBoundaryStabilizer H ξ
    rw [g.val.val.symm_apply_apply]
  exact ⟨i,hconj.symm⟩


/-- In an elementary genuine disc group, every actual hyperbolic element
fixes one common actual boundary point; no finite generation is required. -/
theorem elementary_hyperbolic_common_boundary_fixed_point
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hE : DiscreteGroups.IsElementary H) :
    ∃a : Mobius.ExtendedComplex,∀f : H,Mobius.MobiusHyperbolic f.val→f.val.val a=a := by
  obtain ⟨a,b,hL⟩ := elementary_fuchsianLimitSet_subset_pair H P.discrete hE
  refine ⟨a,?_⟩
  intro f hf
  obtain ⟨c,d,hcd,hfix⟩ := DiscreteGroups.mobius_loxodromic_boundary_fixed_pair f.val hf.1
  have hc : c∈fuchsianLimitSet H:=subset_closure ⟨f,Or.inr hf.1,(hfix c).mpr (Or.inl rfl)⟩
  have hd : d∈fuchsianLimitSet H:=subset_closure ⟨f,Or.inr hf.1,(hfix d).mpr (Or.inr rfl)⟩
  have hca : c=a ∨c=b:=hL hc
  have hda : d=a ∨d=b:=hL hd
  rcases hca with rfl|rfl
  · exact (hfix _).mpr (Or.inl rfl)
  · rcases hda with rfl|rfl
    · exact (hfix _).mpr (Or.inr rfl)
    · exact False.elim (hcd rfl)

/--
The finite-boundary-conjugacy assertion for the full
original finitely generated group scope, with elementary cases retained.
-/
theorem finitelyGenerated_boundary_cyclic_representatives
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG) :
    ∃E : Finset (Subgroup Mobius.complexMobiusGroup),∀K : Subgroup Mobius.complexMobiusGroup,
      IsMaximalCyclicIn H K→∀f : H,f.val∈K→IsBoundaryHyperbolic P.asFuchsianDisc f→
      ∃g : H,DiscreteGroups.Action.Actions.subgroupConjugate g.val K∈E := by
  classical
  by_cases hNE : DiscreteGroups.IsNonElementary H
  · exact finitelyGenerated_nonElementary_boundary_cyclic_representatives P hNE hFG
  · obtain ⟨a,ha⟩ := elementary_hyperbolic_common_boundary_fixed_point P (Classical.not_not.mp hNE)
    refine ⟨{DiscreteGroups.mobiusBoundaryStabilizer H a},?_⟩
    intro K hK f hfK hf
    have hKS:=maximalCyclic_eq_boundaryStabilizer_of_fixed P.asFuchsianDisc K hK f.val hfK hf.1.1.1 a (ha f hf.1)
    refine ⟨1,?_⟩
    have hconj : DiscreteGroups.Action.Actions.subgroupConjugate (1:Mobius.complexMobiusGroup) K=K := by
      ext g
      simp [DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff]
    rw [show (1:H).val=(1:Mobius.complexMobiusGroup) from rfl,hconj,hKS]
    exact Finset.mem_singleton_self _


/-- Literal actual maximal cyclic subgroups containing a genuine boundary
hyperbolic element of the original geometric group. -/
def fuchsianMaximalBoundaryHyperbolicCyclicSubgroups
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : Set (Subgroup Mobius.complexMobiusGroup):=
  {K | IsMaximalCyclicIn H K ∧ ∃f : H,f.val∈K ∧ IsBoundaryHyperbolic D f}

/-- The actual original-group conjugacy relation on the genuine boundary
maximal cyclic subgroups. -/
def fuchsianBoundaryHyperbolicCyclicConjugacySetoid
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    Setoid (fuchsianMaximalBoundaryHyperbolicCyclicSubgroups D) :=
  let _:=mobiusSubgroupConjugationAction H
  Setoid.comap Subtype.val (MulAction.orbitRel H (Subgroup Mobius.complexMobiusGroup))

def FuchsianBoundaryHyperbolicCyclicConjugacyClasses
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H) :=
  Quotient (fuchsianBoundaryHyperbolicCyclicConjugacySetoid D)

/-- A finite actual ambient representative set also bounds a quotient by
a pulled-back equivalence relation, even if the representatives were not
chosen in the original restricted subtype. -/
theorem finite_quotient_comap_of_finite_representatives
    {X Y : Type*} (R : Setoid Y) (f : X→Y) (E : Set Y) (hE : E.Finite)
    (hrep : ∀x : X,∃y∈E,R.r (f x) y) : Finite (Quotient (Setoid.comap f R)) := by
  classical
  let F : Quotient (Setoid.comap f R)→Quotient R:=Quotient.map f (fun _ _ h=>h)
  have hFi : Function.Injective F := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        change Quotient.mk R (f a)=Quotient.mk R (f b) at hab
        apply Quotient.sound
        change R.r (f a) (f b)
        exact Quotient.exact hab
  let S : Set (Quotient R):=Quotient.mk R '' E
  have hS : S.Finite:=hE.image _
  have hFmem (q : Quotient (Setoid.comap f R)) : F q∈S := by
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨y,hy,hxy⟩ := hrep x
      exact ⟨y,hy,(Quotient.sound hxy).symm⟩
  have : Finite S:=hS.to_subtype
  let G : Quotient (Setoid.comap f R)→S:=fun q=>⟨F q,hFmem q⟩
  apply Finite.of_injective G
  intro a b hab
  exact hFi (congrArg Subtype.val hab)

/--
's finite-conjugacy assertion, on the literal actual
maximal-boundary-cyclic class space and with the original FG hypothesis.
-/
theorem finitelyGenerated_boundary_cyclic_classes_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG) :
    Finite (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) := by
  classical
  let _:=mobiusSubgroupConjugationAction H
  obtain ⟨E,hE⟩ := finitelyGenerated_boundary_cyclic_representatives P hFG
  apply finite_quotient_comap_of_finite_representatives
    (MulAction.orbitRel H (Subgroup Mobius.complexMobiusGroup)) Subtype.val (E:Set (Subgroup
      Mobius.complexMobiusGroup)) E.finite_toSet
  intro K
  obtain ⟨f,hfK,hf⟩ := K.property.2
  obtain ⟨g,hg⟩ := hE K.val K.property.1 f hfK hf
  refine ⟨DiscreteGroups.Action.Actions.subgroupConjugate g.val K.val,hg,?_⟩
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  refine ⟨g⁻¹,?_⟩
  change g⁻¹ • (g • K.val)=K.val
  exact inv_smul_smul g K.val

end LowDimensionalTopology.Geometry.Fuchsian
