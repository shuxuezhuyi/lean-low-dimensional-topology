module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Finite convex hulls in the real plane.

Finite sets of planar points admit compact convex hulls and supporting edges. The
lemmas relate extreme points, boundary segments, and finite cyclic descriptions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set

namespace LowDimensionalTopology.Geometry.Euclidean

/-- A genuine nonzero planar normal defines a genuine affine line. -/
theorem complex_inner_level_collinear (n a : ℂ) (hn : n≠0) :
    Collinear ℝ {z : ℂ | inner ℝ n z=inner ℝ n a} := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a,Complex.I*n,?_⟩
  intro z hz
  have horth : inner ℝ n (z-a)=0:=by rw [inner_sub_right,hz,sub_self]
  obtain ⟨t,ht⟩:=complex_orthogonal_eq_real_smul n (z-a) hn horth
  exact ⟨t,sub_eq_iff_eq_add.mp ht⟩

/-- Three distinct genuine extreme points cannot lie on one affine line. -/
theorem three_extreme_points_not_collinear (K : Set ℂ) {a b c : ℂ}
    (ha : a∈K.extremePoints ℝ) (hb : b∈K.extremePoints ℝ) (hc : c∈K.extremePoints ℝ)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) : ¬Collinear ℝ ({a,b,c} : Set ℂ) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · have hopen:=mem_openSegment_of_ne_left_right hab hbc.symm h.mem_segment
    exact hab (hb.2 ha.1 hc.1 hopen)
  · have hopen:=mem_openSegment_of_ne_left_right hbc hac h.mem_segment
    exact hbc (hc.2 hb.1 ha.1 hopen)
  · have hopen:=mem_openSegment_of_ne_left_right hac.symm hab.symm h.mem_segment
    exact hac (ha.2 hc.1 hb.1 hopen).symm

/-- Every extreme vertex of a finite planar hull admits a strict exposing normal,
obtained by real Hahn–Banach separation. -/
theorem finite_extreme_exposing_normal (V : Set ℂ) (hV : V.Finite) (v : ℂ)
    (hv : v∈(convexHull ℝ V).extremePoints ℝ) (hne : (V\{v}).Nonempty) :
    ∃n : ℂ,n≠0 ∧ ∀w∈V,w≠v→inner ℝ n w< inner ℝ n v := by
  have hc : Convex ℝ (convexHull ℝ V):=convex_convexHull ℝ V
  have hvnot : v∉convexHull ℝ (V\{v}):=by
    intro hm
    have hsub : V\{v}⊆convexHull ℝ V\{v}:=fun z hz=>⟨subset_convexHull ℝ V hz.1,hz.2⟩
    exact (hc.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp hv).2 (convexHull_mono hsub hm)
  obtain ⟨f,t,hft,htv⟩:=geometric_hahn_banach_closed_point (convex_convexHull ℝ (V\{v}))
    ((hV.subset sdiff_subset).isClosed_convexHull ℝ) hvnot
  let n : ℂ:=(InnerProductSpace.toDual ℝ ℂ).symm f
  have hn (w : ℂ) : inner ℝ n w=f w:=InnerProductSpace.toDual_symm_apply
  have hstrict (w : ℂ) (hw : w∈V) (hwv : w≠v) : inner ℝ n w< inner ℝ n v:=by
    rw [hn,hn]
    exact (hft w (subset_convexHull ℝ (V\{v}) ⟨hw,hwv⟩)).trans htv
  have hnzero : n≠0:=by
    intro he
    obtain ⟨w,hw⟩:=hne
    have hh:=hstrict w hw.1 hw.2
    rw [he,inner_zero_left,inner_zero_left] at hh
    exact (lt_irrefl _ hh)
  exact ⟨n,hnzero,hstrict⟩

/-- A genuine outgoing support edge of a finite extreme hull, with a proved geometric direction. -/
structure OrientedFiniteHullEdge (V : Finset ℂ) (v w : ℂ) where
  left_mem : v∈V
  right_mem : w∈V
  ne : v≠w
  normal : ℂ
  normal_norm : ‖normal‖=1
  incident : inner ℝ normal w=inner ℝ normal v
  nonincident : ∀u∈V,u≠v→u≠w→inner ℝ normal u < inner ℝ normal v
  direction : ∃a : ℝ,0<a ∧ w-v=a • (Complex.I*normal)

/-- Any self-map of a nonempty finite set has an actual positive-period orbit. -/
theorem finite_selfmap_positive_periodic_point {α : Type*} [Finite α] [Nonempty α]
    (f : α→α) : ∃x : α,0<Function.minimalPeriod f x := by
  classical
  let x₀ : α:=Classical.choice inferInstance
  obtain ⟨i,j,hij,he⟩:=Finite.exists_ne_map_eq_of_infinite (fun n : ℕ=>f^[n] x₀)
  have hstep (i j : ℕ) (hij : i<j) (he : f^[i] x₀=f^[j] x₀) :
      0<Function.minimalPeriod f (f^[i] x₀) := by
    have hp : Function.IsPeriodicPt f (j-i) (f^[i] x₀):=by
      change f^[j-i] (f^[i] x₀)=f^[i] x₀
      rw [←Function.iterate_add_apply,Nat.sub_add_cancel hij.le]
      exact he.symm
    exact hp.minimalPeriod_pos (Nat.sub_pos_of_lt hij)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨f^[i] x₀,hstep i j h he⟩
  · exact ⟨f^[j] x₀,hstep j i h he.symm⟩

/-- A genuine finite planar hull with nonempty actual interior has at least three vertices. -/
theorem finite_planar_hull_card_ge_three (V : Finset ℂ)
    (hn : (interior (convexHull ℝ (V:Set ℂ))).Nonempty) : 3≤V.card := by
  classical
  have hVne : V.Nonempty:=by
    by_contra he
    have hV : V=∅:=Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hV,Finset.coe_empty,convexHull_empty,interior_empty,Set.not_nonempty_empty] at hn
  let : Nonempty V:=⟨⟨hVne.choose,hVne.choose_spec⟩⟩
  have hs : affineSpan ℝ (V:Set ℂ)=⊤:=by
    have hh:=(convex_convexHull ℝ (V:Set ℂ)).interior_nonempty_iff_affineSpan_eq_top.mp hn
    rwa [affineSpan_convexHull] at hh
  have hvec : vectorSpan ℝ (V:Set ℂ)=⊤:=by
    have hh:=congrArg AffineSubspace.direction hs
    simpa only [direction_affineSpan,AffineSubspace.direction_top] using hh
  have hrange : range ((↑) : V→ℂ)=(V:Set ℂ):=by ext z;simp
  have hdim:=finrank_vectorSpan_range_add_one_le ℝ ((↑) : V→ℂ)
  rw [hrange,hvec,finrank_top,Complex.finrank_real_complex,Fintype.card_coe] at hdim
  exact hdim

/-- A true supporting affine line through two distinct genuine extreme points contains no third extreme point. -/
theorem extreme_inner_level_eq_pair (K : Set ℂ) {n v w z : ℂ} (hn : n≠0)
    (hv : v∈K.extremePoints ℝ) (hw : w∈K.extremePoints ℝ) (hz : z∈K.extremePoints ℝ)
    (hvw : v≠w) (hwlevel : inner ℝ n w=inner ℝ n v)
    (hzlevel : inner ℝ n z=inner ℝ n v) : z=v∨z=w := by
  by_contra hnot
  push Not at hnot
  have hcol : Collinear ℝ ({v,w,z} : Set ℂ):=by
    apply (complex_inner_level_collinear n v hn).subset
    intro a ha
    simp only [mem_insert_iff,mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · rfl
    · exact hwlevel
    · exact hzlevel
  exact three_extreme_points_not_collinear K hv hw hz hvw hnot.1.symm hnot.2.symm hcol

/-- Consistent support directions prohibit traversing an edge immediately backwards
when a third extreme point exists. -/
theorem oriented_finite_hull_edge_not_reverse {V : Finset ℂ} {v w : ℂ}
    (E : OrientedFiniteHullEdge V v w) (F : OrientedFiniteHullEdge V w v)
    (hu : ∃u∈V,u≠v ∧ u≠w) : False := by
  obtain ⟨u,hu,huv,huw⟩:=hu
  obtain ⟨a,ha,hE⟩:=E.direction
  obtain ⟨b,hb,hF⟩:=F.direction
  have hlin : Complex.I*(a • E.normal+b • F.normal)=
      a • (Complex.I*E.normal)+b • (Complex.I*F.normal):=by
    simp only [Complex.real_smul]
    ring
  have hIz : Complex.I*(a • E.normal+b • F.normal)=0:=by
    rw [hlin,←hE,←hF]
    abel
  have hN : a • E.normal+b • F.normal=0:=(mul_eq_zero.mp hIz).resolve_left Complex.I_ne_zero
  have hEneg : inner ℝ E.normal (u-v)<0:=by
    rw [inner_sub_right]
    exact sub_neg.mpr (E.nonincident u hu huv huw)
  have hFneg : inner ℝ F.normal (u-v)<0:=by
    rw [inner_sub_right,F.incident]
    exact sub_neg.mpr (F.nonincident u hu huw huv)
  have hs:=congrArg (fun z : ℂ=>inner ℝ z (u-v)) hN
  simp only [inner_add_left,real_inner_smul_left,inner_zero_left] at hs
  have h1:=mul_neg_of_pos_of_neg ha hEneg
  have h2:=mul_neg_of_pos_of_neg hb hFneg
  linarith

/-- A finite map without fixed points or two-cycles produces an injective cyclic
orbit of length at least three. -/
theorem finite_selfmap_nontrivial_cycle {α : Type*} [Finite α] [Nonempty α]
    (f : α→α) (hfixed : ∀x,f x≠x) (htwo : ∀x,f (f x)≠x) :
    ∃n : ℕ,3≤n ∧ ∃v : Fin n→α,Function.Injective v ∧
      ∀i,v (finRotate n i)=f (v i) := by
  obtain ⟨x,hp⟩:=finite_selfmap_positive_periodic_point f
  let p:=Function.minimalPeriod f x
  have hthree : 3≤p:=by
    by_contra hlt
    have hp0 : p≠0:=hp.ne'
    have hp1 : p≠1:=by
      intro he
      exact hfixed x ((Function.minimalPeriod_eq_one_iff_isFixedPt).mp he)
    have hp2 : p=2:=by omega
    have he:=Function.iterate_minimalPeriod (f:=f) (x:=x)
    change f^[p] x=x at he
    rw [hp2] at he
    have hff : f (f x)=x:=by simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using he
    exact htwo x hff
  obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hm' : p=m+1:=hm
  let v (i : Fin (m+1)):=f^[i.val] x
  have hinj : Function.Injective v:=by
    intro i j he
    apply Fin.ext
    have hi : i.val<Function.minimalPeriod f x:=by rw [hm];exact i.isLt
    have hj : j.val<Function.minimalPeriod f x:=by rw [hm];exact j.isLt
    exact Function.iterate_injOn_Iio_minimalPeriod hi hj he
  refine ⟨m+1,hm' ▸ hthree,v,hinj,?_⟩
  intro i
  by_cases hi : i=Fin.last m
  · subst i
    rw [finRotate_last]
    change x=f (f^[m] x)
    have he:=Function.iterate_minimalPeriod (f:=f) (x:=x)
    change f^[p] x=x at he
    rw [hm',Function.iterate_succ_apply'] at he
    exact he.symm
  · change f^[((finRotate (m+1) i).val)] x=f (f^[i.val] x)
    rw [coe_finRotate_of_ne_last hi,Function.iterate_succ_apply']

/-- Rotate a strict exposing normal to its first supporting edge, with a consistent
positive boundary direction. No cyclic order or edge is supplied. -/
theorem finite_exposed_oriented_support (V : Finset ℂ) (K : Set ℂ)
    (hext : ∀u∈V,u∈K.extremePoints ℝ) (v : ℂ) (hv : v∈V)
    (n₀ : ℂ) (hn₀ : n₀≠0) (hstrict : ∀u∈V,u≠v→inner ℝ n₀ u < inner ℝ n₀ v)
    (hne : ∃u∈V,u≠v) :
    ∃w∈V,w≠v ∧ ∃n : ℂ,n≠0 ∧ inner ℝ n w=inner ℝ n v ∧
      (∀u∈V,u≠v→u≠w→inner ℝ n u < inner ℝ n v) ∧
      ∃a : ℝ,0<a ∧ w-v=a • (Complex.I*n) := by
  classical
  obtain ⟨u₀,hu₀,hu₀v⟩:=hne
  let A (u : ℂ):=inner ℝ n₀ (v-u)
  have hA (u : ℂ) (hu : u∈V) (huv : u≠v) : 0<A u:=by
    change 0 < inner ℝ n₀ (v-u)
    rw [inner_sub_right]
    exact sub_pos.mpr (hstrict u hu huv)
  let b:=inner ℝ (Complex.I*n₀) (u₀-v)
  let ε:=A u₀/(2*(|b|+1))
  have hε : 0<ε:=div_pos (hA u₀ hu₀ hu₀v) (by positivity)
  have hεeq : ε*(2*(|b|+1))=A u₀:=div_mul_cancel₀ _ (by positivity)
  let d : ℂ:=(-2:ℝ) • n₀+ε • (Complex.I*n₀)
  let B (u : ℂ):=inner ℝ d (u-v)
  have hB₀ : B u₀=2*A u₀+ε*b:=by
    change inner ℝ ((-2:ℝ) • n₀+ε • (Complex.I*n₀)) (u₀-v)=
      2*inner ℝ n₀ (v-u₀)+ε*inner ℝ (Complex.I*n₀) (u₀-v)
    simp only [inner_add_left,real_inner_smul_left,inner_sub_right]
    ring
  have hB₀pos : 0<B u₀:=by
    have hbnd:=mul_nonneg hε.le (show 0≤b+|b| by linarith [neg_abs_le b])
    rw [hB₀]
    nlinarith [hA u₀ hu₀ hu₀v]
  let F:=V.filter (fun u=>0<B u)
  have hFne : F.Nonempty:=⟨u₀,Finset.mem_filter.mpr ⟨hu₀,hB₀pos⟩⟩
  obtain ⟨w,hwF,hmin⟩:=Finset.exists_min_image F (fun u=>A u/B u) hFne
  have hw : w∈V:=(Finset.mem_filter.mp hwF).1
  have hBw : 0<B w:=(Finset.mem_filter.mp hwF).2
  have hwv : w≠v:=by
    intro he
    have hbv : B v=0:=by simp only [B,sub_self,inner_zero_right]
    have hh : B w=0:=congrArg B he |>.trans hbv
    linarith
  let τ:=A w/B w
  have hτ : 0<τ:=div_pos (hA w hw hwv) hBw
  have hτw : τ*B w=A w:=div_mul_cancel₀ _ hBw.ne'
  let n : ℂ:=n₀+τ • d
  have hrel (u : ℂ) : inner ℝ n u-inner ℝ n v= -A u+τ*B u:=by
    change inner ℝ (n₀+τ • d) u-inner ℝ (n₀+τ • d) v=
      -inner ℝ n₀ (v-u)+τ*inner ℝ d (u-v)
    simp only [inner_add_left,real_inner_smul_left,inner_sub_right]
    ring
  have hlevel : inner ℝ n w=inner ℝ n v:=by
    have hh:=hrel w
    rw [hτw] at hh
    linarith
  have hle (u : ℂ) (hu : u∈V) : inner ℝ n u≤ inner ℝ n v:=by
    by_cases huv : u=v
    · exact huv ▸ le_refl _
    by_cases huB : 0<B u
    · have hm:=hmin u (Finset.mem_filter.mpr ⟨hu,huB⟩)
      change τ≤A u/B u at hm
      have hh:=(le_div_iff₀ huB).mp hm
      linarith [hrel u]
    · have hprod:=mul_nonpos_of_nonneg_of_nonpos hτ.le (le_of_not_gt huB)
      linarith [hA u hu huv,hrel u]
  have horth : inner ℝ n₀ (Complex.I*n₀)=0:=by simp [Complex.inner];ring
  have hself : 0< inner ℝ n₀ n₀:=real_inner_self_pos.mpr hn₀
  have hnform : n=(1-2*τ) • n₀+(τ*ε) • (Complex.I*n₀):=by
    change n₀+τ • ((-2:ℝ) • n₀+ε • (Complex.I*n₀))=_
    module
  have hIform : Complex.I*n=(1-2*τ) • (Complex.I*n₀)-(τ*ε) • n₀:=by
    rw [hnform]
    simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hcross : inner ℝ n₀ (Complex.I*n)= -(τ*ε)*inner ℝ n₀ n₀:=by
    rw [hIform,inner_sub_right,real_inner_smul_right,real_inner_smul_right,horth]
    ring
  have hcrossNeg : inner ℝ n₀ (Complex.I*n)<0:=by
    rw [hcross]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hτ hε)) hself
  have hn : n≠0:=by
    intro he
    rw [he,mul_zero,inner_zero_right] at hcrossNeg
    exact (lt_irrefl _ hcrossNeg)
  have hsharp (u : ℂ) (hu : u∈V) (huv : u≠v) (huw : u≠w) :
      inner ℝ n u < inner ℝ n v:=by
    apply lt_of_le_of_ne (hle u hu)
    intro he
    rcases extreme_inner_level_eq_pair K hn (hext v hv) (hext w hw) (hext u hu)
      hwv.symm hlevel he with he | he
    · exact huv he
    · exact huw he
  have hnormal : inner ℝ n (w-v)=0:=by rw [inner_sub_right,hlevel,sub_self]
  obtain ⟨a,ha⟩:=complex_orthogonal_eq_real_smul n (w-v) hn hnormal
  have hprod : a*inner ℝ n₀ (Complex.I*n)<0:=by
    rw [←real_inner_smul_right,←ha,inner_sub_right]
    exact sub_neg.mpr (hstrict w hw hwv)
  have haPos : 0<a:=by
    by_contra hnpos
    have hnonneg:=mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hnpos) hcrossNeg.le
    linarith
  exact ⟨w,hw,hwv,n,hn,hlevel,hsharp,a,haPos,ha⟩

/-- Genuine finite extreme hull data produce an actual unit-normal outgoing support edge with consistent orientation. -/
theorem finite_extreme_unit_oriented_support (V : Finset ℂ)
    (hext : ∀u∈V,u∈(convexHull ℝ (V:Set ℂ)).extremePoints ℝ)
    (v : ℂ) (hv : v∈V) (hne : ∃u∈V,u≠v) :
    ∃w∈V,w≠v ∧ ∃n : ℂ,‖n‖=1 ∧ inner ℝ n w=inner ℝ n v ∧
      (∀u∈V,u≠v→u≠w→inner ℝ n u < inner ℝ n v) ∧
      ∃a : ℝ,0<a ∧ w-v=a • (Complex.I*n) := by
  have hnempty : ((V:Set ℂ)\{v}).Nonempty:=by
    obtain ⟨u,hu,huv⟩:=hne
    exact ⟨u,hu,huv⟩
  obtain ⟨n₀,hn₀,hstrict⟩:=finite_extreme_exposing_normal (V:Set ℂ) V.finite_toSet v (hext v hv) hnempty
  obtain ⟨w,hw,hwv,n,hn,hlevel,hsharp,a,ha,hdir⟩:=
    finite_exposed_oriented_support V (convexHull ℝ (V:Set ℂ)) hext v hv n₀ hn₀ hstrict hne
  have hnorm : 0<‖n‖:=norm_pos_iff.mpr hn
  let c : ℝ:=‖n‖⁻¹
  have hc : 0<c:=inv_pos.mpr hnorm
  have hcNorm : ‖c • n‖=1:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    exact inv_mul_cancel₀ hnorm.ne'
  have hcLevel : inner ℝ (c • n) w=inner ℝ (c • n) v:=by
    rw [real_inner_smul_left,real_inner_smul_left,hlevel]
  have hcSharp (u : ℂ) (hu : u∈V) (huv : u≠v) (huw : u≠w) :
      inner ℝ (c • n) u < inner ℝ (c • n) v:=by
    rw [real_inner_smul_left,real_inner_smul_left]
    exact mul_lt_mul_of_pos_left (hsharp u hu huv huw) hc
  have hI : Complex.I*(c • n)=c • (Complex.I*n):=by simp only [Complex.real_smul];ring
  have hcDir : w-v=(a*‖n‖) • (Complex.I*(c • n)):=by
    rw [hI,smul_smul]
    have he : a*‖n‖*c=a:=by dsimp [c];field_simp
    rwa [he]
  exact ⟨w,hw,hwv,c • n,hcNorm,hcLevel,hcSharp,a*‖n‖,mul_pos ha hnorm,hcDir⟩

/-- The genuine outgoing support edge is constructed from finite actual extreme points. -/
theorem exists_oriented_finite_hull_edge (V : Finset ℂ)
    (hext : ∀u∈V,u∈(convexHull ℝ (V:Set ℂ)).extremePoints ℝ)
    (v : ℂ) (hv : v∈V) (hne : ∃u∈V,u≠v) :
    ∃w : ℂ,Nonempty (OrientedFiniteHullEdge V v w) := by
  obtain ⟨w,hw,hwv,n,hn,hlevel,hsharp,a,ha,hdir⟩:=finite_extreme_unit_oriented_support V hext v hv hne
  exact ⟨w,⟨⟨hv,hw,hwv.symm,n,hn,hlevel,hsharp,a,ha,hdir⟩⟩⟩

end LowDimensionalTopology.Geometry.Euclidean
