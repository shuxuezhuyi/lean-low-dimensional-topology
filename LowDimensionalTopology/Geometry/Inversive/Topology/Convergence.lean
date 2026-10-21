/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.Topology.NormalFamilies
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Three-point subsequential convergence

Three distinct source points with distinct limiting images give an
equicontinuous family in the actual chordal space. A pointwise limit with
three distinct values is injective, preserves real cross ratios, and
therefore belongs to the reflection-generated general Möbius group.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology Uniformity OnePoint
namespace LowDimensionalTopology.Geometry.Inversive

theorem positive_lower_bound_of_convergent {a : ℕ → ℝ} {b : ℝ}
    (h : Tendsto a atTop (𝓝 b)) (ha : ∀ k,0<a k) (hb : 0<b) :
    ∃ ε : ℝ, 0<ε ∧ ∀ k, ε≤a k := by
  obtain ⟨ε,hε,hbound⟩ := h.isCompact_insert_range.exists_forall_le'
    (f := id) continuous_id.continuousOn (a := 0) (by
      intro x hx
      rcases hx with rfl | ⟨k,rfl⟩
      · exact hb
      · exact ha k)
  exact ⟨ε,hε,fun k => hbound _ (by simp)⟩

variable {n : ℕ}
local instance limitsChordalMetric : MetricSpace (ExtendedEuclidean n) := chordalMetricSpace n

theorem mobius_pair_uniform_separated_of_tendsto (F : ℕ → GM n)
    {a b y z : ExtendedEuclidean n} (hab : a≠b) (hyz : y≠z)
    (ha : Tendsto (fun k => (F k : ExtendedHomeomorph n) a) atTop (𝓝 y))
    (hb : Tendsto (fun k => (F k : ExtendedHomeomorph n) b) atTop (𝓝 z)) :
    ∃ ε : ℝ,0<ε ∧ ∀ k,ε≤chordalDist ((F k : ExtendedHomeomorph n) a)
      ((F k : ExtendedHomeomorph n) b) :=
  positive_lower_bound_of_convergent (ha.dist hb)
    (fun k => chordalDist_positive ((F k : ExtendedHomeomorph n).injective.ne hab))
    (chordalDist_positive hyz)

theorem pointwiseLimit_preservesRealCrossRatios (F : ℕ → GM n)
    (f : ExtendedEuclidean n → ExtendedEuclidean n) (hf : Function.Injective f)
    (hconv : ∀ x,Tendsto (fun k => (F k : ExtendedHomeomorph n) x) atTop (𝓝 (f x))) :
    PreservesRealCrossRatios f := by
  intro x y u v hd
  have hden : dist (f x) (f y)*dist (f u) (f v)≠0 :=
    mul_ne_zero (dist_ne_zero.mpr (hf.ne hd.1)) (dist_ne_zero.mpr (hf.ne hd.2.2.2.2.2))
  have hlim := ((hconv x).dist (hconv u)).mul ((hconv y).dist (hconv v))
  have hlimden := ((hconv x).dist (hconv y)).mul ((hconv u).dist (hconv v))
  have heq : (fun k => realCrossRatio ((F k : ExtendedHomeomorph n) x)
      ((F k : ExtendedHomeomorph n) y) ((F k : ExtendedHomeomorph n) u)
      ((F k : ExtendedHomeomorph n) v)) = fun _ => realCrossRatio x y u v := by
    funext k
    convert generalMobius_preservesRealCrossRatios (F k) (F k).property x y u v hd using 1
  have hh := hlim.div hlimden hden
  change Tendsto (fun k => realCrossRatio ((F k : ExtendedHomeomorph n) x)
      ((F k : ExtendedHomeomorph n) y) ((F k : ExtendedHomeomorph n) u)
      ((F k : ExtendedHomeomorph n) v)) atTop (𝓝 (realCrossRatio (f x) (f y) (f u) (f v))) at hh
  rw [heq] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

theorem threeAnchors_avoiding_pair (x : Fin 3 → ExtendedEuclidean n)
    (hx : Function.Injective x) (p : ExtendedEuclidean n) :
    ∃ i j : Fin 3, i≠j ∧ p≠x i ∧ p≠x j := by
  by_cases h0 : p=x 0
  · exact ⟨1,2,by decide,by simpa only [h0] using hx.ne (by decide : (0 : Fin 3)≠1),
      by simpa only [h0] using hx.ne (by decide : (0 : Fin 3)≠2)⟩
  by_cases h1 : p=x 1
  · exact ⟨0,2,by decide,h0,by simpa only [h1] using hx.ne (by decide : (1 : Fin 3)≠2)⟩
  exact ⟨0,1,by decide,h0,h1⟩

theorem pointwiseLimit_injective_of_three_distinct_values (F : ℕ → GM n)
    (f : ExtendedEuclidean n → ExtendedEuclidean n)
    (hconv : ∀ x,Tendsto (fun k => (F k : ExtendedHomeomorph n) x) atTop (𝓝 (f x)))
    (a : Fin 3 → ExtendedEuclidean n) (ha : Function.Injective (fun i => f (a i))) :
    Function.Injective f := by
  intro x y hxy
  by_contra hne
  obtain ⟨i,j,hij,h0i,h0j⟩ := threeAnchors_avoiding_pair (fun i => f (a i)) ha (f x)
  have hxa : x≠a i := fun h => h0i (congrArg f h)
  have hxb : x≠a j := fun h => h0j (congrArg f h)
  have hya : y≠a i := fun h => h0i (hxy.trans (congrArg f h))
  have hyb : y≠a j := fun h => h0j (hxy.trans (congrArg f h))
  have hab : a i≠a j := fun h => hij (ha (congrArg f h))
  have hd : FourDistinct x (a i) y (a j) := ⟨hxa,hne,hxb,hya.symm,hab,hyb⟩
  have hfyb : f y≠f (a j) := fun h => h0j (hxy.trans h)
  have hden : dist (f x) (f (a i))*dist (f y) (f (a j))≠0 :=
    mul_ne_zero (dist_ne_zero.mpr h0i) (dist_ne_zero.mpr hfyb)
  have hlim := (((hconv x).dist (hconv y)).mul ((hconv (a i)).dist (hconv (a j)))).div
    (((hconv x).dist (hconv (a i))).mul ((hconv y).dist (hconv (a j)))) hden
  have heq : (fun k => realCrossRatio ((F k : ExtendedHomeomorph n) x)
      ((F k : ExtendedHomeomorph n) (a i)) ((F k : ExtendedHomeomorph n) y)
      ((F k : ExtendedHomeomorph n) (a j))) = fun _ => realCrossRatio x (a i) y (a j) := by
    funext k
    convert generalMobius_preservesRealCrossRatios (F k) (F k).property x (a i) y (a j) hd using 1
  change Tendsto (fun k => realCrossRatio ((F k : ExtendedHomeomorph n) x)
      ((F k : ExtendedHomeomorph n) (a i)) ((F k : ExtendedHomeomorph n) y)
      ((F k : ExtendedHomeomorph n) (a j))) atTop
    (𝓝 (realCrossRatio (f x) (f (a i)) (f y) (f (a j)))) at hlim
  rw [heq] at hlim
  have hv := tendsto_nhds_unique tendsto_const_nhds hlim
  have hz : realCrossRatio (f x) (f (a i)) (f y) (f (a j))=0 := by
    simp [realCrossRatio,hxy,chordalDist]
  exact (ne_of_gt (realCrossRatio_positive hd)) (hv.trans hz)

theorem pointwiseLimit_generalMobius_of_three_distinct_values [NeZero n] (F : ℕ → GM n)
    (f : ExtendedEuclidean n → ExtendedEuclidean n)
    (hconv : ∀ x,Tendsto (fun k => (F k : ExtendedHomeomorph n) x) atTop (𝓝 (f x)))
    (a : Fin 3 → ExtendedEuclidean n) (ha : Function.Injective (fun i => f (a i))) :
    ∃ g : GM n, (fun z => (g : ExtendedHomeomorph n) z)=f := by
  have hinj := pointwiseLimit_injective_of_three_distinct_values F f hconv a ha
  obtain ⟨g,hg,hge⟩ := (preservesRealCrossRatios_iff_generalMobius f).mp
    (pointwiseLimit_preservesRealCrossRatios F f hinj hconv)
  exact ⟨⟨g,hg⟩,hge⟩

theorem mobius_equicontinuous_of_threePointConvergence (F : ℕ → GM n)
    (x y : Fin 3 → ExtendedEuclidean n) (hx : Function.Injective x) (hy : Function.Injective y)
    (hconv : ∀ j,Tendsto (fun k => (F k : ExtendedHomeomorph n) (x j)) atTop (𝓝 (y j))) :
    Equicontinuous (fun k z => (F k : ExtendedHomeomorph n) z) := by
  classical
  intro p
  obtain ⟨i,j,hij,hpi,hpj⟩ := threeAnchors_avoiding_pair x hx p
  obtain ⟨ε,hε,hsep⟩ := mobius_pair_uniform_separated_of_tendsto F (hx.ne hij) (hy.ne hij)
    (hconv i) (hconv j)
  let D : Set (ExtendedEuclidean n) := {x i,x j}ᶜ
  have hD : IsOpen D := by
    have hfin : ({x i,x j} : Set (ExtendedEuclidean n)).Finite := by simp
    exact hfin.isClosed.isOpen_compl
  have hp : p∈D := by simp [D,hpi,hpj]
  have hDc : Dᶜ.Nonempty := ⟨x i,by simp [D]⟩
  have hclear : 0<Metric.infDist p Dᶜ := (hD.isClosed_compl.notMem_iff_infDist_pos hDc).mp
    (by simpa only [Set.mem_compl_iff,not_not] using hp)
  let r : ℝ := Metric.infDist p Dᶜ/2
  have hr : 0<r := half_pos hclear
  have hnear : ∀ᶠ z in 𝓝 p,r<Metric.infDist z Dᶜ :=
    (Metric.continuous_infDist_pt Dᶜ).continuousAt.eventually
      (eventually_gt_nhds (show r<Metric.infDist p Dᶜ from half_lt_self hclear))
  rw [Metric.equicontinuousAt_iff_right]
  intro η hη
  let C : ℝ := 8/(ε*r)
  have hC : 0<C := div_pos (by norm_num) (mul_pos hε hr)
  have hball : ∀ᶠ z in 𝓝 p,dist p z<η/C := by
    have hsmall : ∀ᶠ z in 𝓝 p,dist z p<η/C := Metric.ball_mem_nhds p (div_pos hη hC)
    filter_upwards [hsmall] with z hz
    rwa [dist_comm] at hz
  filter_upwards [hD.mem_nhds hp,hnear,hball] with z hz hzr hzp k
  have ha : (F k : ExtendedHomeomorph n) (x i) ∉ (F k : ExtendedHomeomorph n) '' D := by
    rintro ⟨w,hw,he⟩
    have he' := (F k : ExtendedHomeomorph n).injective he
    subst w
    simp [D] at hw
  have hb : (F k : ExtendedHomeomorph n) (x j) ∉ (F k : ExtendedHomeomorph n) '' D := by
    rintro ⟨w,hw,he⟩
    have he' := (F k : ExtendedHomeomorph n).injective he
    subst w
    simp [D] at hw
  have hbound := generalMobius_omitted_distortion_uniform (F k) (F k).property D hD
    ((F k : ExtendedHomeomorph n) (x i)) ((F k : ExtendedHomeomorph n) (x j))
    ε r hε hr ha hb (hsep k) p z hp hz (by dsimp [r]; linarith) hzr.le
  change dist ((F k : ExtendedHomeomorph n) p) ((F k : ExtendedHomeomorph n) z)<η
  exact hbound.trans_lt (by change C*dist p z<η; nlinarith [(lt_div_iff₀ hC).mp hzp])

theorem mobius_subsequence_of_threePointConvergence [NeZero n] (F : ℕ → GM n)
    (x y : Fin 3 → ExtendedEuclidean n) (hx : Function.Injective x) (hy : Function.Injective y)
    (hconv : ∀ j,Tendsto (fun k => (F k : ExtendedHomeomorph n) (x j)) atTop (𝓝 (y j))) :
    ∃ φ : ℕ → ℕ,StrictMono φ ∧ ∃ g : GM n,
      TendstoUniformly (fun k z => (F (φ k) : ExtendedHomeomorph n) z)
        (fun z => (g : ExtendedHomeomorph n) z) atTop := by
  have heq := mobius_equicontinuous_of_threePointConvergence F x y hx hy hconv
  have hnormal : NormalFamily (fun k z => (F k : ExtendedHomeomorph n) z) :=
    normalFamily_of_compactwise_equicontinuous (fun K _ => heq.equicontinuousOn K)
  obtain ⟨φ,hφ,f,hf⟩ := hnormal id
  have hu := tendstoUniformlyOn_univ.mp (hf univ isCompact_univ)
  have hvalues : ∀ j,f (x j)=y j := fun j =>
    tendsto_nhds_unique (hu.tendsto_at (x j)) ((hconv j).comp hφ.tendsto_atTop)
  have hinj : Function.Injective (fun j => f (x j)) := by
    intro i j h
    apply hy
    rw [← hvalues i,← hvalues j]
    exact h
  obtain ⟨g,hg⟩ := pointwiseLimit_generalMobius_of_three_distinct_values
    (fun k => F (φ k)) f (fun z => hu.tendsto_at z) x hinj
  refine ⟨φ,hφ,g,?_⟩
  rw [hg]
  exact hu

end LowDimensionalTopology.Geometry.Inversive
