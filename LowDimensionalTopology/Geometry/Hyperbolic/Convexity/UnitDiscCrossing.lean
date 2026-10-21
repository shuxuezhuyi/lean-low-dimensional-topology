module
public import LowDimensionalTopology.External.LeanPool.Schoenflies.JordanClosed
public import LowDimensionalTopology.External.LeanPool.Schoenflies.AccessibleJoin
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Algebra.Field.Periodic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric Schoenflies
open scoped Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing

/-- An actual connected trace approaching opposite arcs of a Jordan crosscut must meet it. -/
theorem crosscut_intersection {C P A B Q : Set Plane} {p q c d : Plane}
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A B)
    (hQ : IsPreconnected Q) (hsub : Q ⊆ inside C)
    (hc : c ∈ closure Q) (hd : d ∈ closure Q)
    (hcA : c ∈ A) (hcB : c ∉ B) (hdB : d ∈ B) (hdA : d ∉ A) :
    (Q ∩ P).Nonempty := by
  by_contra hne
  have hQP : Q ⊆ inside C \ P := fun z hz => ⟨hsub hz,fun hp => hne ⟨z,hz,hp⟩⟩
  obtain ⟨heq,_hdis,_hAn,_hBn,_hne,hccA,hccB,_hex,hclA,hclB⟩ := crosscut_theorem h hcut
  obtain ⟨z,hz⟩ : Q.Nonempty := by
    by_contra hnone
    rw [not_nonempty_iff_eq_empty.mp hnone,closure_empty] at hc
    exact hc
  have hzU : z ∈ inside (A ∪ P) ∪ inside (B ∪ P) := by rw [←heq];exact hQP hz
  rcases hzU with hzA | hzB
  · have hQA : Q ⊆ inside (A ∪ P) := by
      have hh := hQ.subset_connectedComponentIn hz hQP
      rwa [hccA z hzA] at hh
    have hdc : d ∈ closure (inside (A ∪ P)) ∩ C := ⟨closure_mono hQA hd,hcut.snd_subset hdB⟩
    rw [hclA] at hdc
    exact hdA hdc
  · have hQB : Q ⊆ inside (B ∪ P) := by
      have hh := hQ.subset_connectedComponentIn hz hQP
      rwa [hccB z hzB] at hh
    have hcc : c ∈ closure (inside (B ∪ P)) ∩ C := ⟨closure_mono hQB hc,hcut.fst_subset hcA⟩
    rw [hclB] at hcc
    exact hcB hcc


/-- The standard genuine round circle is a Jordan curve in the real plane. -/
theorem unitSphere_isJordanCurve : IsJordanCurve (sphere (0 : Plane) 1) := by
  let f (t : ℝ) : Plane := Complex.orthonormalBasisOneI.repr (Circle.exp (2*Real.pi*t) : ℂ)
  have hc : Continuous f := Complex.orthonormalBasisOneI.repr.continuous.comp
    (continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id)))
  have hloop : IsLoop f := by
    refine ⟨hc.continuousOn,?_,?_⟩
    · simp [f]
    · intro a ha b hb hab
      have he : Circle.exp (2*Real.pi*a) = Circle.exp (2*Real.pi*b) :=
        Subtype.ext (Complex.orthonormalBasisOneI.repr.injective hab)
      have harg := (Circle.exp_injOn_Ico (a := 0) (b := 2*Real.pi) (by linarith))
        (show 2*Real.pi*a ∈ Ico 0 (2*Real.pi) by
          constructor <;> nlinarith [Real.pi_pos,ha.1,ha.2])
        (show 2*Real.pi*b ∈ Ico 0 (2*Real.pi) by
          constructor <;> nlinarith [Real.pi_pos,hb.1,hb.2]) he
      nlinarith [Real.pi_pos]
  refine ⟨f,hloop,Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨t,_ht,rfl⟩
    rw [mem_sphere_zero_iff_norm]
    exact (Complex.orthonormalBasisOneI.repr.norm_map _).trans (Circle.norm_coe _)
  · intro z hz
    have hzn : ‖Complex.orthonormalBasisOneI.repr.symm z‖ = 1 := by
      rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp hz
    let u : Circle := ⟨Complex.orthonormalBasisOneI.repr.symm z,mem_sphere_zero_iff_norm.mpr hzn⟩
    have hu : u ∈ Circle.exp '' Icc 0 (2*Real.pi) := by
      rw [show Icc 0 (2*Real.pi) = Icc 0 (0+2*Real.pi) by simp,
        Circle.periodic_exp.image_Icc (by positivity),Circle.exp_surjective.range_eq]
      trivial
    obtain ⟨s,hs,he⟩ := hu
    refine ⟨s/(2*Real.pi),?_,?_⟩
    · constructor
      · exact div_nonneg hs.1 (by positivity)
      · exact (div_le_one (by positivity : 0<2*Real.pi)).mpr hs.2
    · change Complex.orthonormalBasisOneI.repr (Circle.exp (2*Real.pi*(s/(2*Real.pi))) : ℂ) = z
      rw [mul_div_cancel₀ _ (by positivity : 2*Real.pi≠0),he]
      exact Complex.orthonormalBasisOneI.repr.apply_symm_apply z

/-- The bounded complementary region is the actual open unit ball. -/
theorem inside_unitSphere : inside (sphere (0 : Plane) 1) = ball 0 1 := by
  have hsep := jordan_curve_theorem unitSphere_isJordanCurve
  have hcc : connectedComponentIn (sphere (0 : Plane) 1)ᶜ (0:Plane) = ball 0 1 := by
    apply Plane.connectedComponentIn_eq_of_frontier_disjoint isOpen_ball (convex_ball (0:Plane) 1).isPreconnected
    · intro z hz
      exact ne_of_lt (mem_ball.mp hz)
    · rw [frontier_ball (0:Plane) (by norm_num : (1:ℝ)≠0),inter_compl_self]
    · exact mem_ball_self (by norm_num)
  have hz : (0:Plane) ∈ inside (sphere (0:Plane) 1) := by
    refine ⟨?_,?_⟩
    · norm_num
    · rw [hcc];exact isBounded_ball
  exact (hsep.connectedComponentIn_eq_inside hz).symm.trans hcc

/-- A boundary point of a connected trace is polygonally accessible in the complementary component of a disjoint closed set. -/
theorem ball_component_accessible {A B : Set Plane} (hA : IsPreconnected A)
    (hAball : A ⊆ ball 0 1) (hB : IsClosed B) (hAB : Disjoint (closure A) B)
    {x a : Plane} (hx : x ∈ A) (ha : a ∈ closure A) (has : a ∈ sphere 0 1) :
    PolyAccessible (connectedComponentIn (ball 0 1 ∩ Bᶜ) x) a := by
  let U := ball (0:Plane) 1 ∩ Bᶜ
  let W := connectedComponentIn U x
  have hAsub : A ⊆ U := fun z hz => ⟨hAball hz,fun hzB => Set.disjoint_left.mp hAB (subset_closure hz) hzB⟩
  have hAW : A ⊆ W := hA.subset_connectedComponentIn hx hAsub
  have haB : a ∉ B := fun haB => Set.disjoint_left.mp hAB ha haB
  obtain ⟨ε,hε,hsmall⟩ := Metric.isOpen_iff.mp hB.isOpen_compl a haB
  obtain ⟨q,hqa,hq⟩ := mem_closure_iff_nhds.mp ha _ (isOpen_ball.mem_nhds (mem_ball_self hε))
  have hqW : q ∈ W := hAW hq
  let V := ball a ε ∩ ball (0:Plane) 1
  have hVsub : V ⊆ U := fun z hz => ⟨hz.2,hsmall hz.1⟩
  have hVconn : IsPreconnected V := ((convex_ball a ε).inter (convex_ball (0:Plane) 1)).isPreconnected
  have hVW : V ⊆ W := by
    have hcomp := hVconn.subset_connectedComponentIn ⟨hqa,hAball hq⟩ hVsub
    rwa [←connectedComponentIn_eq hqW] at hcomp
  apply PolyAccessible.of_openSegment hqW
  intro z hz
  apply hVW
  refine ⟨(convex_ball a ε).segment_subset (mem_ball_self hε) hqa (openSegment_subset_segment ℝ a q hz),?_⟩
  have hs := (convex_ball (0:Plane) 1).openSegment_interior_closure_subset_interior
    (by rw [isOpen_ball.interior_eq];exact hAball hq)
    (by rw [closure_ball (0:Plane) (by norm_num : (1:ℝ)≠0)];exact sphere_subset_closedBall has)
  have hz' : z ∈ openSegment ℝ q a := by rwa [openSegment_symm]
  simpa only [isOpen_ball.interior_eq] using hs hz'


/-- Two traces with alternating limiting endpoints in the actual round ball have intersecting closures. -/
theorem alternating_ball_traces_closures_intersect {A B C D : Set Plane} {a b c d : Plane}
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAball : A ⊆ ball 0 1) (hBball : B ⊆ ball 0 1)
    (ha : a ∈ closure A) (hb : b ∈ closure A)
    (hcut : IsCutPair (sphere (0:Plane) 1) a b C D)
    (hc : c ∈ closure B) (hd : d ∈ closure B)
    (hcC : c ∈ C) (hcD : c ∉ D) (hdD : d ∈ D) (hdC : d ∉ C) :
    (closure A ∩ closure B).Nonempty := by
  by_contra hne
  have hdis : Disjoint (closure A) (closure B) := Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)
  obtain ⟨x,hx⟩ : A.Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty.mp hempty,closure_empty] at ha
    exact ha
  let U := ball (0:Plane) 1 ∩ (closure B)ᶜ
  let W := connectedComponentIn U x
  have hWopen : IsOpen W := (isOpen_ball.inter isClosed_closure.isOpen_compl).connectedComponentIn
  have hWasub : W ⊆ ball 0 1 := fun z hz => (connectedComponentIn_subset U x hz).1
  have hWavoid : W ⊆ (closure B)ᶜ := fun z hz => (connectedComponentIn_subset U x hz).2
  have haS := hcut.fst_subset hcut.fst.left_mem
  have hbS := hcut.fst_subset hcut.fst.right_mem
  have haW : PolyAccessible W a := ball_component_accessible hA hAball isClosed_closure hdis hx ha haS
  have hbW : PolyAccessible W b := ball_component_accessible hA hAball isClosed_closure hdis hx hb hbS
  obtain ⟨P,hpoly,harc,hP⟩ := exists_simple_arc_of_polyAccessible hWopen isPreconnected_connectedComponentIn
    hcut.fst.ne haW hbW
  have hcross : IsCrosscut (sphere (0:Plane) 1) P a b :=
    ⟨unitSphere_isJordanCurve,harc,hpoly,haS,hbS,fun z hz => by rw [inside_unitSphere];exact hWasub (hP hz)⟩
  obtain ⟨z,hzB,hzP⟩ := crosscut_intersection hcross hcut hB
    (by rw [inside_unitSphere];exact hBball) hc hd hcC hcD hdD hdC
  by_cases hzend : z ∈ ({a,b}:Set Plane)
  · rcases hzend with rfl | rfl
    · exact Set.disjoint_left.mp hdis ha (subset_closure hzB)
    · exact Set.disjoint_left.mp hdis hb (subset_closure hzB)
  · exact hWavoid (hP ⟨hzP,hzend⟩) (subset_closure hzB)

end LowDimensionalTopology.Geometry.Hyperbolic.PlaneCrossing
