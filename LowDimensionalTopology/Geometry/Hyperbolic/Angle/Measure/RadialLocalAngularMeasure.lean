module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.LocalAngularMeasure
public import Mathlib.Topology.Connected.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc ENNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The genuine native disc coordinate is an open embedding in the complex plane. -/
theorem disc_coe_isOpenEmbedding : Topology.IsOpenEmbedding ((↑) : Complex.UnitDisc→ℂ) := by
  refine ⟨Complex.UnitDisc.isEmbedding_coe,?_⟩
  have hrange : range ((↑) : Complex.UnitDisc→ℂ)={p : ℂ | ‖p‖<1}:=by
    ext z
    constructor
    · rintro ⟨p,rfl⟩;exact p.norm_lt_one
    · intro hz;exact ⟨Complex.UnitDisc.mk z hz,rfl⟩
  rw [hrange]
  exact isOpen_lt continuous_norm continuous_const

/-- Membership is constant along a genuinely connected set avoiding the actual frontier. -/
theorem preconnected_membership_iff_of_avoids_frontier {X : Type*} [TopologicalSpace X]
    {T A : Set X} (hT : IsPreconnected T) (hAvoid : ∀p∈T,p∉frontier A)
    {x y : X} (hx : x∈T) (hy : y∈T) : x∈A ↔y∈A := by
  have hs : T⊆interior A∪interior Aᶜ := by
    intro p hp
    rw [←compl_frontier_eq_union_interior]
    exact hAvoid p hp
  have hd : Disjoint (interior A) (interior Aᶜ):=Set.disjoint_left.mpr
    (fun _ ha hc=>interior_subset hc (interior_subset ha))
  rcases IsPreconnected.subset_or_subset isOpen_interior isOpen_interior hd hs hT with h | h
  · exact iff_of_true (interior_subset (h hx)) (interior_subset (h hy))
  · exact iff_of_false (interior_subset (h hx)) (interior_subset (h hy))

/-- Along any genuine radial interval avoiding the actual frontier, membership in
an arbitrary original disc set is independent of positive radius. -/
theorem discRadialPoint_mem_iff_of_avoids_frontier (S : Set Complex.UnitDisc)
    (R : Ioo (0 : ℝ) 1) (u : Circle)
    (hu : u∉discRadialDirections (frontier S∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))
    (r s : Ioo (0 : ℝ) 1) (hr : r.val<R.val) (hs : s.val<R.val) :
    discRadialPoint r u∈S ↔discRadialPoint s u∈S := by
  let f : Ioo (0 : ℝ) R.val→Complex.UnitDisc:=fun t=>
    discRadialPoint ⟨t.val,⟨t.property.1,lt_trans t.property.2 R.property.2⟩⟩ u
  have hc : Continuous f:=by
    apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const
  let : PreconnectedSpace (Ioo (0 : ℝ) R.val):=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hp : IsPreconnected (range f):=isPreconnected_range hc
  have ha : ∀p∈range f,p∉frontier S := by
    rintro p ⟨t,rfl⟩ ht
    apply hu
    refine ⟨⟨t.val,⟨t.property.1,lt_trans t.property.2 R.property.2⟩⟩,ht,?_⟩
    change ‖(f t : ℂ)‖<R.val
    rw [discRadialPoint_norm]
    exact t.property.2
  exact preconnected_membership_iff_of_avoids_frontier hp ha
    ⟨⟨r.val,⟨r.property.1,hr⟩⟩,rfl⟩ ⟨⟨s.val,⟨s.property.1,hs⟩⟩,rfl⟩

/-- If actual frontier directions in a genuine origin ball have angular measure zero,
the local angle is exactly the angular measure of membership on a true small circle.
No convexity, prescribed angle, or overlap count is assumed. -/
theorem discLocalAngularFraction_eq_radial_measure_of_frontier_null
    (S : Set Complex.UnitDisc) (R : Ioo (0 : ℝ) 1)
    (hNull : polygonDirectionMeasure
      (discRadialDirections (frontier S∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))=0) :
    discLocalAngularFraction S 0=
      polygonDirectionMeasure (discRadialPoint
        ⟨R.val/2,⟨div_pos R.property.1 (by norm_num),by nlinarith [R.property.2]⟩⟩ ⁻¹' S) := by
  let r₀ : Ioo (0 : ℝ) 1:=⟨R.val/2,⟨div_pos R.property.1 (by norm_num),by nlinarith [R.property.2]⟩⟩
  let Q : Set Circle:=discRadialPoint r₀ ⁻¹' S
  have hr₀ : r₀.val<R.val:=by dsimp [r₀];linarith [R.property.1]
  have hball (t : Ioo (0 : ℝ) 1) (ht : t.val≤R.val) :
      polygonDirectionMeasure (discRadialDirections (S∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<t.val}))=
        polygonDirectionMeasure Q := by
    apply measure_congr
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hNull)] with u hu
    apply propext
    constructor
    · rintro ⟨r,hrS,hrBall⟩
      have hrt : r.val<t.val:=by
        change ‖(discRadialPoint r u : ℂ)‖<t.val at hrBall
        simpa only [discRadialPoint_norm] using hrBall
      exact (discRadialPoint_mem_iff_of_avoids_frontier S R u hu r r₀
        (lt_of_lt_of_le hrt ht) hr₀).mp hrS
    · intro huQ
      let r : Ioo (0 : ℝ) 1:=⟨t.val/2,⟨div_pos t.property.1 (by norm_num),by nlinarith [t.property.2]⟩⟩
      have hrt : r.val<t.val:=by dsimp [r];linarith [t.property.1]
      have hrR : r.val<R.val:=lt_of_lt_of_le hrt ht
      refine ⟨r,(discRadialPoint_mem_iff_of_avoids_frontier S R u hu r r₀ hrR hr₀).mpr huQ,?_⟩
      change ‖(discRadialPoint r u : ℂ)‖<t.val
      simpa only [discRadialPoint_norm] using hrt
  have hRpos:=R.property.1
  have hNR : {p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}∈𝓝 (0 : Complex.UnitDisc):=by
    exact (isOpen_lt (continuous_norm.comp Complex.UnitDisc.continuous_coe)
      continuous_const).mem_nhds (by
        change ‖((0 : Complex.UnitDisc) : ℂ)‖<R.val
        rw [Complex.UnitDisc.coe_zero,norm_zero]
        exact R.property.1)
  change discLocalAngularFraction S 0=polygonDirectionMeasure Q
  apply le_antisymm
  · apply (discLocalAngularFraction_le S 0 ({p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val})
      hNR).trans_eq
    rw [discSubtendedAngularFraction_zero]
    exact hball R le_rfl
  · apply le_iInf
    intro N
    have hNimage:=disc_coe_isOpenEmbedding.image_mem_nhds.mpr N.property
    obtain ⟨δ,hδ,hδN⟩:=Metric.mem_nhds_iff.mp hNimage
    let t : Ioo (0 : ℝ) 1:=⟨min (δ/2) (R.val/2),⟨by positivity,by
      have hh:=min_le_right (δ/2) (R.val/2);nlinarith [R.property.2]⟩⟩
    have htR : t.val≤R.val:=by
      have hh:=min_le_right (δ/2) (R.val/2);dsimp [t];linarith [R.property.1]
    have htδ : t.val≤δ:=by
      have hh:=min_le_left (δ/2) (R.val/2);dsimp [t];linarith
    calc
      polygonDirectionMeasure Q=
          polygonDirectionMeasure (discRadialDirections (S∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<t.val})) :=(hball t
            htR).symm
      _=discSubtendedAngularFraction (S∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<t.val}) 0 :=
        (discSubtendedAngularFraction_zero _).symm
      _≤discSubtendedAngularFraction (S∩N.val) 0 :=by
        apply discSubtendedAngularFraction_mono
        apply inter_subset_inter_right S
        intro p hp
        have himg : (p : ℂ)∈((↑) : Complex.UnitDisc→ℂ) '' N.val:=hδN (by
          change dist (p : ℂ) (0 : ℂ)<δ
          rw [dist_zero_right]
          exact lt_of_lt_of_le hp htδ)
        exact Complex.UnitDisc.coe_injective.mem_set_image.mp himg

/-- Finitely many actual supporting geodesics give one genuine origin ball in which
all actual frontier directions have zero angular measure. Nonincident geodesics are
excluded by their genuine closedness; incident geodesics have finitely many directions. -/
theorem finite_discLine_frontier_radial_null {ι J : Type*} [Finite J]
    (S : ι→Set Complex.UnitDisc) (L : J→DiscLine)
    (hFrontier : ∀i,frontier (S i)⊆⋃j,(L j).carrier) :
    ∃R : Ioo (0 : ℝ) 1,∀i,polygonDirectionMeasure
      (discRadialDirections (frontier (S i)∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))=0 := by
  classical
  let : Fintype J:=Fintype.ofFinite J
  let N : Set Complex.UnitDisc:={p | ∀j,p∈(L j).carrier →(0 : Complex.UnitDisc)∈(L j).carrier}
  have hN : N∈𝓝 (0 : Complex.UnitDisc):=by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : (0 : Complex.UnitDisc)∈(L j).carrier
    · exact Filter.Eventually.of_forall (fun _ _=>hj)
    · filter_upwards [(L j).isClosed_carrier.isOpen_compl.mem_nhds hj] with p hp hLine
      exact (hp hLine).elim
  have hnImage:=disc_coe_isOpenEmbedding.image_mem_nhds.mpr hN
  obtain ⟨δ,hδ,hδN⟩:=Metric.mem_nhds_iff.mp hnImage
  let R : Ioo (0 : ℝ) 1:=⟨min (δ/2) (1/2),⟨by positivity,by
    have hh:=min_le_right (δ/2) (1/2 : ℝ);linarith⟩⟩
  have hRδ : R.val≤δ:=by
    have hh:=min_le_left (δ/2) (1/2 : ℝ);dsimp [R];linarith
  have hball : {p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}⊆N:=by
    intro p hp
    have himg : (p : ℂ)∈((↑) : Complex.UnitDisc→ℂ) '' N:=hδN (by
      change dist (p : ℂ) (0 : ℂ)<δ
      rw [dist_zero_right]
      exact lt_of_lt_of_le hp hRδ)
    exact Complex.UnitDisc.coe_injective.mem_set_image.mp himg
  have hzero : polygonDirectionMeasure (⋃j : J,{u : Circle |
      (0 : Complex.UnitDisc)∈(L j).carrier ∧u∈discRadialDirections (L j).carrier})=0:=by
    apply measure_iUnion_null
    intro j
    by_cases hj : (0 : Complex.UnitDisc)∈(L j).carrier
    · have he : {u : Circle | (0 : Complex.UnitDisc)∈(L j).carrier ∧
          u∈discRadialDirections (L j).carrier}=discRadialDirections (L j).carrier:=by
        ext u;simp only [mem_ofPred_eq,hj,true_and]
      rw [he]
      exact polygonDirectionMeasure_line_zero (L j) hj
    · simp only [hj,false_and,ofPred_false,measure_empty]
  refine ⟨R,fun i=>measure_mono_null ?_ hzero⟩
  rintro u ⟨r,hrF,hrB⟩
  obtain ⟨j,hj⟩:=mem_iUnion.mp (hFrontier i hrF)
  exact mem_iUnion.mpr ⟨j,hball hrB j hj,⟨r,hj⟩⟩

/-- The genuine local angles of a finite measurable family sum to the literal radial
membership count integrated on the true direction circle. -/
theorem finite_local_angular_sum_of_radial_count {ι : Type*} [Fintype ι]
    (S : ι→Set Complex.UnitDisc) (R : Ioo (0 : ℝ) 1)
    (hS : ∀i,MeasurableSet (S i))
    (hNull : ∀i,polygonDirectionMeasure
      (discRadialDirections (frontier (S i)∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))=0)
    (k : ℝ≥0∞)
    (hCount : ∀ᵐu ∂polygonDirectionMeasure,
      (∑i,(discRadialPoint ⟨R.val/2,⟨div_pos R.property.1 (by norm_num),by
        nlinarith [R.property.2]⟩⟩ ⁻¹' S i).indicator (fun _ : Circle=>(1 : ℝ≥0∞)) u)=k) :
    (∑i,discLocalAngularFraction (S i) 0)=k := by
  classical
  let r : Ioo (0 : ℝ) 1:=⟨R.val/2,⟨div_pos R.property.1 (by norm_num),by nlinarith [R.property.2]⟩⟩
  let Q (i : ι) : Set Circle:=discRadialPoint r ⁻¹' S i
  have hQ (i : ι) : MeasurableSet (Q i):=(hS i).preimage (continuous_discRadialPoint r).measurable
  calc
    (∑i,discLocalAngularFraction (S i) 0)=∑i,polygonDirectionMeasure (Q i) :=
      Finset.sum_congr rfl (fun i _=>discLocalAngularFraction_eq_radial_measure_of_frontier_null
        (S i) R (hNull i))
    _=∑i,∫⁻u,(Q i).indicator (fun _ : Circle=>(1 : ℝ≥0∞)) u ∂polygonDirectionMeasure :=
      Finset.sum_congr rfl (fun i _=>(lintegral_indicator_one (hQ i)).symm)
    _=∫⁻u,∑i,(Q i).indicator (fun _ : Circle=>(1 : ℝ≥0∞)) u ∂polygonDirectionMeasure :=
      (lintegral_finsetSum _ (fun i _=>measurable_const.indicator (hQ i))).symm
    _=∫⁻_u,k ∂polygonDirectionMeasure :=lintegral_congr_ae hCount
    _=k :=by simp

/-- Taking the original inside leaves the genuine local angle unchanged whenever
actual local frontier directions are null. This covers reflex as well as convex germs. -/
theorem discLocalAngularFraction_interior_eq_of_frontier_radial_null
    (S : Set Complex.UnitDisc) (R : Ioo (0 : ℝ) 1)
    (hNull : polygonDirectionMeasure
      (discRadialDirections (frontier S∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))=0) :
    discLocalAngularFraction (interior S) 0=discLocalAngularFraction S 0 := by
  have hNullI : polygonDirectionMeasure
      (discRadialDirections (frontier (interior S)∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))=0 :=
    measure_mono_null (discRadialDirections_mono
      (inter_subset_inter_left _ frontier_interior_subset)) hNull
  rw [discLocalAngularFraction_eq_radial_measure_of_frontier_null _ R hNullI,
    discLocalAngularFraction_eq_radial_measure_of_frontier_null _ R hNull]
  apply measure_congr
  let r : Ioo (0 : ℝ) 1:=⟨R.val/2,⟨div_pos R.property.1 (by norm_num),by nlinarith [R.property.2]⟩⟩
  have hr : r.val<R.val:=by dsimp [r];linarith [R.property.1]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNull] with u hu
  apply propext
  change discRadialPoint r u∈interior S ↔discRadialPoint r u∈S
  constructor
  · intro h;exact interior_subset h
  · intro hs
    apply (mem_interior_iff_notMem_frontier hs).mpr
    intro hf
    apply hu
    refine ⟨r,hf,?_⟩
    change ‖(discRadialPoint r u : ℂ)‖<R.val
    rwa [discRadialPoint_norm]

end LowDimensionalTopology.Geometry.Hyperbolic
