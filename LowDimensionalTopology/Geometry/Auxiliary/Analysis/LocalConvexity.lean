/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Closed connected locally convex sets

A finite-dimensional energy-minimization argument proves convexity. A path gives a finite feasible chain in a compact part
of the closed set. An energy minimizer is fixed by every local midpoint
replacement, hence is a straight chain containing the entire endpoint segment.

Preconnectedness includes the empty convex set. No compactness or uniform
local radius is imposed on the set in the final theorem.
-/

@[expose] public section
noncomputable section
open Set Metric Filter Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every point has an ambient open neighborhood whose intersection with the set is convex. -/
def IsLocallyConvexSet (s : Set E) : Prop :=
  ∀ x ∈ s, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ Convex ℝ (s ∩ U)

theorem Convex.isLocallyConvexSet {s : Set E} (hs : Convex ℝ s) : IsLocallyConvexSet s := by
  intro x hx
  exact ⟨univ,isOpen_univ,mem_univ x,by simpa only [inter_univ] using hs⟩

theorem IsLocallyConvexSet.exists_convex_ball {s : Set E} (hs : IsLocallyConvexSet s)
    {x : E} (hx : x ∈ s) : ∃ r > 0, Convex ℝ (s ∩ ball x r) := by
  obtain ⟨U,hU,hxU,hc⟩ := hs x hx
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hxU
  refine ⟨r,hr,?_⟩
  rw [convex_iff_segment_subset]
  intro y hy z hz w hw
  exact ⟨(hc.segment_subset ⟨hy.1,hball hy.2⟩ ⟨hz.1,hball hz.2⟩ hw).1,
    (convex_ball x r).segment_subset hy.2 hz.2 hw⟩

theorem IsLocallyConvexSet.locallyPathConnectedSpace {s : Set E} (hs : IsLocallyConvexSet s) :
    LocallyPathConnectedSpace s where
  path_connected_basis x := by
    rw [hasBasis_self]
    intro T hT
    obtain ⟨r,hr,hrT⟩ := Metric.mem_nhds_iff.mp hT
    obtain ⟨ε,hε,hconv⟩ := hs.exists_convex_ball x.property
    let δ := min r ε
    have hδ : 0 < δ := lt_min hr hε
    have hc : Convex ℝ (s ∩ ball x.val δ) := by
      rw [convex_iff_segment_subset]
      intro y hy z hz w hw
      exact ⟨(hconv.segment_subset ⟨hy.1,ball_subset_ball (min_le_right r ε) hy.2⟩
        ⟨hz.1,ball_subset_ball (min_le_right r ε) hz.2⟩ hw).1,
        (convex_ball x.val δ).segment_subset hy.2 hz.2 hw⟩
    let W : Set s := Subtype.val ⁻¹' (s ∩ ball x.val δ)
    refine ⟨W,?_,?_,?_⟩
    · apply mem_of_superset (Metric.ball_mem_nhds x hδ)
      intro y hy
      exact ⟨y.property,hy⟩
    · exact (hc.isPathConnected ⟨x.val,x.property,by simpa using hδ⟩).preimage_coe inter_subset_left
    · intro y hy
      apply hrT
      exact ball_subset_ball (min_le_left r ε) hy.2

/-- A compact part of a locally convex set has one radius valid for every local shortcut. -/
theorem IsLocallyConvexSet.exists_uniform_segment_radius {s K : Set E}
    (hs : IsLocallyConvexSet s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ s, ∀ z ∈ s,
      dist y x ≤ δ → dist z x ≤ δ → segment ℝ y z ⊆ s := by
  choose U hU hxU hc using fun x : K => hs x.val (hKs x.property)
  obtain ⟨r,hr,hcover⟩ := Metric.uniformity_basis_dist.lebesgue_number_lemma_nhds'
    (U := fun x hx => U ⟨x,hx⟩) hK (fun x hx => (hU ⟨x,hx⟩).mem_nhds (hxU ⟨x,hx⟩))
  refine ⟨r/2,by positivity,?_⟩
  intro x hx y hy z hz hyx hzx
  obtain ⟨a,ha⟩ := hcover x hx
  apply ((hc a).segment_subset ⟨hy,?_⟩ ⟨hz,?_⟩).trans inter_subset_left
  · apply ha
    change dist x y < r
    rw [dist_comm]
    linarith
  · apply ha
    change dist x z < r
    rw [dist_comm]
    linarith

theorem IsLocallyConvexSet.exists_path {s : Set E} (hs : IsLocallyConvexSet s)
    (hp : IsPreconnected s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ∃ γ : Path x y, ∀ t, γ t ∈ s := by
  let : LocallyPathConnectedSpace s := hs.locallyPathConnectedSpace
  let : ConnectedSpace s := isConnected_iff_connectedSpace.mp ⟨⟨x,hx⟩,hp⟩
  let : PathConnectedSpace s := PathConnectedSpace.of_locallyPathConnectedSpace
  let γ := PathConnectedSpace.somePath (⟨x,hx⟩ : s) (⟨y,hy⟩ : s)
  exact ⟨γ.map continuous_subtype_val,fun t => (γ t).property⟩

/-- Quadratic chain energy with fixed endpoints; the last index is always positive. -/
def polygonEnergy {N : ℕ} (p : Fin (N+2) → E) : ℝ :=
  ∑ i : Fin (N+1), dist (p i.castSucc) (p i.succ)^2

omit [NormedSpace ℝ E] in
theorem polygonEnergy_continuous (N : ℕ) :
    Continuous (polygonEnergy (E:=E) (N:=N)) := by
  unfold polygonEnergy
  fun_prop

/-- The standard finite subdivision of the unit interval. -/
def polygonGridTime (N : ℕ) (i : Fin (N+2)) : unitInterval :=
  ⟨(i.val : ℝ)/(N+1),div_nonneg (by positivity) (by positivity),
    (div_le_one (by positivity : (0:ℝ)<N+1)).mpr (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩

@[simp] theorem polygonGridTime_zero (N : ℕ) : polygonGridTime N 0 = 0 := by
  apply Subtype.ext
  simp [polygonGridTime]

@[simp] theorem polygonGridTime_last (N : ℕ) : polygonGridTime N (Fin.last (N+1)) = 1 := by
  apply Subtype.ext
  simp [polygonGridTime,show (N:ℝ)+1≠0 by positivity]

theorem polygonGridTime_step_dist (N : ℕ) (i : Fin (N+1)) :
    dist (polygonGridTime N i.castSucc) (polygonGridTime N i.succ) = 1/(N+1) := by
  change dist ((i.val : ℝ)/(N+1)) (((i.val+1 : ℕ):ℝ)/(N+1)) = _
  rw [Real.dist_eq]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [← sub_div]
  have h : (i.val : ℝ)-((i.val : ℝ)+1) = -1 := by ring
  rw [h,abs_div,abs_neg,abs_one,abs_of_pos (by positivity : (0:ℝ)<N+1)]

omit [NormedSpace ℝ E] in
theorem path_exists_finite_chain {x y : E} (γ : Path x y) {δ : ℝ} (hδ : 0<δ) :
    ∃ N : ℕ, ∃ p : Fin (N+2) → E, p 0=x ∧ p (Fin.last (N+1))=y ∧
      (∀ i,p i∈range γ) ∧ ∀ i : Fin (N+1),dist (p i.castSucc) (p i.succ)≤δ := by
  have hu : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  obtain ⟨η,hη,hstep⟩ := Metric.uniformContinuous_iff.mp hu δ hδ
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hη
  refine ⟨N,fun i=>γ (polygonGridTime N i),by simp,by simp,?_,?_⟩
  · exact fun i=>mem_range_self _
  · intro i
    exact (hstep (by simpa only [polygonGridTime_step_dist] using hN)).le


section InnerProduct
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem midpoint_energy_identity (a b c : F) :
    dist a b ^ 2 + dist b c ^ 2 =
      dist a (midpoint ℝ a c) ^ 2 + dist (midpoint ℝ a c) c ^ 2 +
        2 * dist b (midpoint ℝ a c) ^ 2 := by
  have h := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq b a c
  rw [dist_comm b a] at h
  rw [dist_left_midpoint,dist_midpoint_right,Real.norm_two]
  nlinarith

/-- A fixed-size chain in a compact set, with fixed endpoints and bounded steps. -/
def polygonFeasible (K : Set F) (δ : ℝ) (a b : F) (N : ℕ) : Set (Fin (N+2) → F) :=
  {p | (∀ i,p i∈K) ∧ p 0=a ∧ p (Fin.last (N+1))=b ∧
    ∀ i : Fin (N+1),dist (p i.castSucc) (p i.succ)≤δ}

omit [InnerProductSpace ℝ F] in
theorem polygonFeasible_isCompact {K : Set F} (hK : IsCompact K)
    (δ : ℝ) (a b : F) (N : ℕ) : IsCompact (polygonFeasible K δ a b N) := by
  have he : polygonFeasible K δ a b N = ((univ.pi (fun _ : Fin (N+2)=>K)) ∩
    ({p | p 0=a} ∩ {p | p (Fin.last (N+1))=b} ∩
      {p | ∀ i : Fin (N+1),dist (p i.castSucc) (p i.succ)≤δ})) := by
    ext p
    simp [polygonFeasible,and_assoc]
  rw [he]
  apply (isCompact_univ_pi (fun _=>hK)).inter_right
  have hc : IsClosed {p : Fin (N+2) → F | ∀ i : Fin (N+1),dist (p i.castSucc) (p i.succ)≤δ} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i =>
      isClosed_le ((continuous_apply i.castSucc).dist (continuous_apply i.succ)) continuous_const)
  exact ((isClosed_eq (continuous_apply 0) continuous_const).inter
    (isClosed_eq (continuous_apply (Fin.last (N+1))) continuous_const)).inter
      hc

/-- One coordinate of the chain is replaced by the midpoint of its two neighbors. -/
def polygonMidpointUpdate {N : ℕ} (p : Fin (N+2) → F) (j : Fin N) : Fin (N+2) → F :=
  Function.update p j.succ.castSucc (midpoint ℝ (p j.castSucc.castSucc) (p j.succ.succ))

theorem polygonEnergy_midpoint_update {N : ℕ} (p : Fin (N+2) → F) (j : Fin N) :
    polygonEnergy (polygonMidpointUpdate p j) +
      2*dist (p j.succ.castSucc) (midpoint ℝ (p j.castSucc.castSucc) (p j.succ.succ))^2 =
        polygonEnergy p := by
  classical
  let q := polygonMidpointUpdate p j
  have hne : j.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; simp at this
  have hd : polygonEnergy p - polygonEnergy q =
      (dist (p j.castSucc.castSucc) (p j.castSucc.succ)^2-
        dist (q j.castSucc.castSucc) (q j.castSucc.succ)^2) +
      (dist (p j.succ.castSucc) (p j.succ.succ)^2-
        dist (q j.succ.castSucc) (q j.succ.succ)^2) := by
    rw [polygonEnergy,polygonEnergy,← Finset.sum_sub_distrib]
    apply Finset.sum_eq_add_of_mem j.castSucc j.succ (Finset.mem_univ _) (Finset.mem_univ _) hne
    intro i _ hi
    have hleft : i.castSucc ≠ j.succ.castSucc := by
      intro he
      exact hi.2 (Fin.castSucc_injective _ he)
    have hright : i.succ ≠ j.succ.castSucc := by
      intro he
      apply hi.1
      apply Fin.ext
      change i.val=j.val
      have hh := congrArg Fin.val he
      simp only [Fin.val_succ,Fin.val_castSucc] at hh
      change i.val+1=j.val+1 at hh
      omega
    simp only [q,polygonMidpointUpdate,Function.update_of_ne hleft,Function.update_of_ne hright,sub_self]
  have hprev : j.castSucc.castSucc ≠ j.succ.castSucc := by intro h; have := congrArg Fin.val h; simp at this
  have hnext : j.succ.succ ≠ j.succ.castSucc := by intro h; have := congrArg Fin.val h; simp at this
  have hcenter : j.castSucc.succ = j.succ.castSucc := by rfl
  simp only [q,polygonMidpointUpdate,hcenter,Function.update_self,
    Function.update_of_ne hprev,Function.update_of_ne hnext] at hd
  have he := midpoint_energy_identity (p j.castSucc.castSucc) (p j.succ.castSucc) (p j.succ.succ)
  dsimp only [polygonMidpointUpdate]
  linarith only [hd,he]


/-- Local midpoint shortcuts preserve the same compact feasible chain space. -/
theorem polygonMidpointUpdate_mem_feasible {K : Set F} {δ : ℝ} {a b : F} {N : ℕ}
    {p : Fin (N+2) → F} (hp : p∈polygonFeasible K δ a b N)
    (hmid : ∀ x∈K,∀ y∈K,∀ z∈K,dist y x≤δ→dist z x≤δ→midpoint ℝ y z∈K)
    (j : Fin N) : polygonMidpointUpdate p j ∈ polygonFeasible K δ a b N := by
  classical
  obtain ⟨hpK,hp0,hplast,hsteps⟩ := hp
  have hprev : j.castSucc.castSucc ≠ j.succ.castSucc := by intro h; have := congrArg Fin.val h; simp at this
  have hnext : j.succ.succ ≠ j.succ.castSucc := by intro h; have := congrArg Fin.val h; simp at this
  have hcenter : j.castSucc.succ = j.succ.castSucc := rfl
  have hleft : dist (p j.castSucc.castSucc) (p j.succ.castSucc)≤δ := hsteps j.castSucc
  have hright : dist (p j.succ.castSucc) (p j.succ.succ)≤δ := hsteps j.succ
  have hmK : midpoint ℝ (p j.castSucc.castSucc) (p j.succ.succ)∈K :=
    hmid _ (hpK _) _ (hpK _) _ (hpK _) hleft (by rw [dist_comm]; exact hright)
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i=j.succ.castSucc
    · subst i
      simpa only [polygonMidpointUpdate,Function.update_self] using hmK
    · simpa only [polygonMidpointUpdate,Function.update_of_ne hi] using hpK i
  · have h0 : (0 : Fin (N+2))≠j.succ.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      change 0=j.val+1 at hv
      omega
    simpa only [polygonMidpointUpdate,Function.update_of_ne h0] using hp0
  · have hl : Fin.last (N+1)≠j.succ.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      change N+1=j.val+1 at hv
      omega
    simpa only [polygonMidpointUpdate,Function.update_of_ne hl] using hplast
  · intro i
    have ht := dist_triangle (p j.castSucc.castSucc) (p j.succ.castSucc) (p j.succ.succ)
    by_cases hi : i=j.castSucc
    · subst i
      simp only [polygonMidpointUpdate,hcenter,Function.update_of_ne hprev,Function.update_self]
      rw [dist_left_midpoint,Real.norm_two]
      nlinarith
    · by_cases hi' : i=j.succ
      · subst i
        simp only [polygonMidpointUpdate,Function.update_of_ne hnext,Function.update_self]
        rw [dist_midpoint_right,Real.norm_two]
        nlinarith
      · have hl : i.castSucc≠j.succ.castSucc := fun he=>hi' (Fin.castSucc_injective _ he)
        have hr : i.succ≠j.succ.castSucc := by
          intro he
          apply hi
          apply Fin.ext
          change i.val=j.val
          have hh := congrArg Fin.val he
          change i.val+1=j.val+1 at hh
          omega
        simpa only [polygonMidpointUpdate,Function.update_of_ne hl,Function.update_of_ne hr] using hsteps i

/-- An energy minimizer is discrete harmonic at every interior vertex. -/
theorem polygon_energy_minimizer_midpoint {K : Set F} {δ : ℝ} {a b : F} {N : ℕ}
    {p : Fin (N+2) → F} (hp : p∈polygonFeasible K δ a b N)
    (hmin : IsMinOn polygonEnergy (polygonFeasible K δ a b N) p)
    (hmid : ∀ x∈K,∀ y∈K,∀ z∈K,dist y x≤δ→dist z x≤δ→midpoint ℝ y z∈K)
    (j : Fin N) : p j.succ.castSucc = midpoint ℝ (p j.castSucc.castSucc) (p j.succ.succ) := by
  have hle := hmin (polygonMidpointUpdate_mem_feasible hp hmid j)
  have he := polygonEnergy_midpoint_update p j
  change polygonEnergy p ≤ polygonEnergy (polygonMidpointUpdate p j) at hle
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x:=p j.succ.castSucc) (y:=midpoint ℝ (p j.castSucc.castSucc) (p j.succ.succ))]


/-- A finite harmonic chain has constant increments. -/
theorem polygon_harmonic_linear {N : ℕ} (p : Fin (N+2) → F)
    (hp : ∀ j : Fin N,p j.succ.castSucc=midpoint ℝ (p j.castSucc.castSucc) (p j.succ.succ)) :
    ∃ d : F,∀ i : Fin (N+2),p i=p 0+(i.val : ℝ)•d := by
  let d := p (0 : Fin (N+1)).succ-p 0
  have hstep : ∀ j : Fin N,
      p j.succ.succ-p j.succ.castSucc=p j.castSucc.succ-p j.castSucc.castSucc := by
    intro j
    have h := hp j
    rw [midpoint_eq_smul_add,invOf_eq_inv] at h
    change p j.succ.succ-p j.succ.castSucc=p j.succ.castSucc-p j.castSucc.castSucc
    linear_combination (norm := module) (-2:ℝ) • h
  have he : ∀ i : Fin (N+1),p i.succ-p i.castSucc=d := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j hj => exact (hstep j).trans hj
  refine ⟨d,?_⟩
  intro i
  induction i using Fin.induction with
  | zero => simp
  | succ j hj =>
    have h := he j
    change p j.castSucc=p 0+(j.val : ℝ)•d at hj
    simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
    change p j.succ=p 0+((j.val : ℝ)+1)•d
    linear_combination (norm := module) h+hj

/-- A point on the full affine line splits a segment into two covering subsegments. -/
theorem segment_subset_union_of_mem_line {a b c : F}
    (hc : c∈range (AffineMap.lineMap a b : ℝ→F)) :
    segment ℝ a b ⊆ segment ℝ a c ∪ segment ℝ c b := by
  rw [← insert_endpoints_openSegment]
  apply insert_subset_iff.mpr
  refine ⟨Or.inl (left_mem_segment ℝ a c),?_⟩
  apply insert_subset_iff.mpr
  refine ⟨Or.inr (right_mem_segment ℝ c b),?_⟩
  intro z hz
  obtain he|he := openSegment_subset_union a b hc hz
  · subst z
    exact Or.inl (right_mem_segment ℝ a c)
  · rcases he with hl|hr
    · exact Or.inl (openSegment_subset_segment ℝ a c hl)
    · exact Or.inr (openSegment_subset_segment ℝ c b hr)

/-- A straight harmonic chain whose edges lie in a set contains the entire endpoint segment. -/
theorem polygon_segment_subset_of_harmonic {s : Set F} {N : ℕ} (p : Fin (N+2) → F)
    (h0 : p 0∈s) (hseg : ∀ i : Fin (N+1),segment ℝ (p i.castSucc) (p i.succ)⊆s)
    (hp : ∀ j : Fin N,p j.succ.castSucc=midpoint ℝ (p j.castSucc.castSucc) (p j.succ.succ)) :
    segment ℝ (p 0) (p (Fin.last (N+1)))⊆s := by
  obtain ⟨d,hd⟩ := polygon_harmonic_linear p hp
  have h : ∀ i : Fin (N+2),segment ℝ (p 0) (p i)⊆s := by
    intro i
    induction i using Fin.induction with
    | zero => simpa only [segment_same,singleton_subset_iff] using h0
    | succ j hj =>
      have hline : p j.castSucc∈range (AffineMap.lineMap (p 0) (p j.succ) : ℝ→F) := by
        refine ⟨(j.val : ℝ)/(j.val+1),?_⟩
        rw [AffineMap.lineMap_apply_module',hd j.succ,hd j.castSucc]
        simp only [Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one,add_sub_cancel_left,smul_smul]
        rw [div_mul_cancel₀ _ (by positivity : (j.val : ℝ)+1≠0)]
        exact add_comm _ _
      exact (segment_subset_union_of_mem_line hline).trans (union_subset hj (hseg j))
  exact h _


/-- Tietze–Nakajima in finite-dimensional real inner-product spaces. -/
theorem convex_of_isClosed_isPreconnected_isLocallyConvex [FiniteDimensional ℝ F]
    {s : Set F} (hclosed : IsClosed s) (hconn : IsPreconnected s) (hlocal : IsLocallyConvexSet s) :
    Convex ℝ s := by
  rw [convex_iff_segment_subset]
  intro a ha b hb
  obtain ⟨γ,hγ⟩ := hlocal.exists_path hconn ha hb
  obtain ⟨R,hR⟩ := (isCompact_range γ.continuous).isBounded.subset_closedBall a
  let K := s∩closedBall a R
  have hK : IsCompact K := (isCompact_closedBall a R).inter_left hclosed
  obtain ⟨δ,hδ,hshortcut⟩ := hlocal.exists_uniform_segment_radius hK inter_subset_left
  obtain ⟨N,q,hq0,hqlast,hqrange,hqsteps⟩ := path_exists_finite_chain γ hδ
  have hq : q∈polygonFeasible K δ a b N := by
    refine ⟨?_,hq0,hqlast,hqsteps⟩
    intro i
    obtain ⟨t,ht⟩ := hqrange i
    exact ⟨ht ▸ hγ t,hR (hqrange i)⟩
  obtain ⟨p,hp,hmin⟩ := (polygonFeasible_isCompact hK δ a b N).exists_isMinOn
    ⟨q,hq⟩ (polygonEnergy_continuous N).continuousOn
  have hmid : ∀ x∈K,∀ y∈K,∀ z∈K,dist y x≤δ→dist z x≤δ→midpoint ℝ y z∈K := by
    intro x hx y hy z hz hyx hzx
    refine ⟨hshortcut x hx y hy.1 z hz.1 hyx hzx (midpoint_mem_segment (𝕜:=ℝ) y z),?_⟩
    exact (convex_closedBall a R).midpoint_mem hy.2 hz.2
  have hseg : ∀ i : Fin (N+1),segment ℝ (p i.castSucc) (p i.succ)⊆s := by
    intro i
    exact hshortcut _ (hp.1 i.castSucc) _ (hp.1 i.castSucc).1 _ (hp.1 i.succ).1
      (by simpa using hδ.le) (by rw [dist_comm]; exact hp.2.2.2 i)
  have hfull := polygon_segment_subset_of_harmonic p (hp.1 0).1 hseg
    (polygon_energy_minimizer_midpoint hp hmin hmid)
  simpa only [hp.2.1,hp.2.2.1] using hfull

theorem convex_iff_isPreconnected_isLocallyConvex_of_isClosed [FiniteDimensional ℝ F]
    {s : Set F} (hs : IsClosed s) :
    Convex ℝ s ↔ IsPreconnected s ∧ IsLocallyConvexSet s := by
  exact ⟨fun h=>⟨h.isPreconnected,Convex.isLocallyConvexSet h⟩,
    fun h=>convex_of_isClosed_isPreconnected_isLocallyConvex hs h.1 h.2⟩


end InnerProduct

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
