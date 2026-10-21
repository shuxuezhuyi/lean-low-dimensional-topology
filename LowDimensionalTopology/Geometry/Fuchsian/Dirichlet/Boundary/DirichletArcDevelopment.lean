module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletOrbitBoundary
public import Mathlib.Topology.Algebra.ConstMulAction
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Pointwise unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The actual accumulated change of original tiles along successive paired arcs. -/
def pathDevelopmentTransform {G : Type*} [Group G] (t : ℕ → G) : ℕ → G
  | 0 => 1
  | n + 1 => pathDevelopmentTransform t n * (t n)⁻¹

/-- The actual endpoint identification makes consecutive translated arcs meet. -/
theorem pathDevelopmentTransform_endpoint {G X : Type*} [Group G] [MulAction G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1)) (n : ℕ) :
    pathDevelopmentTransform t (n + 1) • x (n + 1) =
      pathDevelopmentTransform t n • b n := by
  rw [pathDevelopmentTransform, ←ht n, mul_smul, inv_smul_smul]

/-- A genuine concatenated path in the original carrier, obtained by translating
successive actual paths so that their endpoints coincide. -/
def equivariantPathDevelopment {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) : ∀ n, Path (x 0) (pathDevelopmentTransform t n • x n)
  | 0 => (Path.refl (x 0)).cast rfl (by simp [pathDevelopmentTransform])
  | n + 1 => (equivariantPathDevelopment x b t ht γ n).trans
      (((γ n).map (continuous_const_smul (pathDevelopmentTransform t n))).cast rfl
        (pathDevelopmentTransform_endpoint x b t ht n))

/-- Each new actual arc is appended to, rather than merely associated with, the previous path. -/
theorem equivariantPathDevelopment_range_succ {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (n : ℕ) :
    range (equivariantPathDevelopment x b t ht γ (n + 1)) =
      range (equivariantPathDevelopment x b t ht γ n) ∪
        pathDevelopmentTransform t n • range (γ n) := by
  rw [equivariantPathDevelopment, Path.trans_range]
  congr 1
  change range ((fun u => pathDevelopmentTransform t n • u) ∘ γ n) = _
  rw [range_comp]
  rfl

/-- Actual invariance of a subset keeps the entire developed path in that subset. -/
theorem equivariantPathDevelopment_range_subset {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (S : Set X)
    (hS : ∀ g : G, ∀ u ∈ S, g • u ∈ S) (hx : x 0 ∈ S)
    (hγ : ∀ n, range (γ n) ⊆ S) (n : ℕ) :
    range (equivariantPathDevelopment x b t ht γ n) ⊆ S := by
  induction n with
  | zero =>
      rintro u ⟨s,rfl⟩
      exact hx
  | succ n ih =>
      rw [equivariantPathDevelopment_range_succ]
      apply union_subset ih
      rintro u ⟨v,hv,rfl⟩
      exact hS _ _ (hγ n hv)

/-- A genuine finite endpoint cycle produces an actual path from its initial point
to the actual accumulated group translate of that same point. -/
def equivariantCycleDevelopment {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (n : ℕ) (hcycle : x n = x 0) :
    Path (x 0) (pathDevelopmentTransform t n • x 0) :=
  (equivariantPathDevelopment x b t ht γ n).cast rfl (congrArg (fun u => pathDevelopmentTransform t n • u) hcycle.symm)

/-- Each developed initial segment is literally contained in every later developed path. -/
theorem equivariantPathDevelopment_range_monotone {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) :
    Monotone (fun n => range (equivariantPathDevelopment x b t ht γ n)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [equivariantPathDevelopment_range_succ]
  exact subset_union_left

/-- A positive actual development contains its entire actual first arc. -/
theorem equivariantPathDevelopment_firstArc_subset {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (n : ℕ) (hn : 0 < n) :
    range (γ 0) ⊆ range (equivariantPathDevelopment x b t ht γ n) := by
  have hfirst : range (γ 0) ⊆ range (equivariantPathDevelopment x b t ht γ 1) := by
    rw [equivariantPathDevelopment_range_succ]
    intro u hu
    right
    simpa only [pathDevelopmentTransform, one_smul] using hu
  exact hfirst.trans (equivariantPathDevelopment_range_monotone x b t ht γ hn)

/-- The true finite-cycle path remains in every actual invariant set containing its arcs. -/
theorem equivariantCycleDevelopment_range_subset {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (x b : ℕ → X) (t : ℕ → G) (ht : ∀ n, t n • b n = x (n + 1))
    (γ : ∀ n, Path (x n) (b n)) (n : ℕ) (hcycle : x n = x 0)
    (S : Set X) (hS : ∀ g : G, ∀ u ∈ S, g • u ∈ S) (hx : x 0 ∈ S)
    (hγ : ∀ n, range (γ n) ⊆ S) :
    range (equivariantCycleDevelopment x b t ht γ n hcycle) ⊆ S :=
  equivariantPathDevelopment_range_subset x b t ht γ S hS hx hγ n

/-- An actual finite alternating Dirichlet endpoint cycle develops into a genuine
original-carrier path from its initial point to one actual group translate of that point.
Its entire image lies on the literal full-orbit neighborhood frontier and contains an
actual injective initial component arc, whose interior lies inside the original polygon. -/
theorem dirichlet_circle_pairings_develop_actual_paths
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) (hR : 0 < R)
    (u : Circle)
    (hu : u ∉ closure ((fun z => (fuchsianMetricCircleHomeomorph P w R hR z).val) ⁻¹'
      dirichletDomain P w))
    (E : ↥(frontier ((fun z => (fuchsianMetricCircleHomeomorph P w R hR z).val) ⁻¹'
      dirichletDomain P w)) ≃ dirichletCircleCuts P w R)
    (hE : ∀ p, (E p).val = (fuchsianMetricCircleHomeomorph P w R hR p.val).val)
    (a b : Equiv.Perm (dirichletCircleCuts P w R))
    (hpair : ∀ x, ∃ k : H, k ≠ 1 ∧ k • x.val = (a x).val)
    (harc : ∀ x, circleArcEndpointNeighbor
      ((fun z => (fuchsianMetricCircleHomeomorph P w R hR z).val) ⁻¹' dirichletDomain P w)
      (E.symm x).val (E.symm (b x)).val)
    (N : ℕ) (hN : 0 < N) (hperiod : (a*b)^N = 1)
    (x₀ : dirichletCircleCuts P w R) :
    ∃ k : H, ∃ Γ : Path x₀.val (k • x₀.val),
      range Γ ⊆ frontier (fuchsianOrbitBallUnion P w R) ∧
      ∃ δ : Path x₀.val (b x₀).val, Function.Injective δ ∧ range δ ⊆ range Γ ∧
        range δ \ {x₀.val,(b x₀).val} ⊆ dirichletDomain P w := by
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  let xs : ℕ → dirichletCircleCuts P w R := fun n => ((a*b)^n) x₀
  let x : ℕ → P.domain.carrier := fun n => (xs n).val
  let y : ℕ → P.domain.carrier := fun n => (b (xs n)).val
  have heval (z : dirichletCircleCuts P w R) :
      (fuchsianMetricCircleHomeomorph P w R hR (E.symm z).val).val = z.val := by
    simpa only [E.apply_symm_apply] using (hE (E.symm z)).symm
  have hpaths (n : ℕ) : ∃ δ : Path (x n) (y n), Function.Injective δ ∧
      range δ ⊆ frontier (fuchsianOrbitBallUnion P w R) ∧
      range δ \ {x n,y n} ⊆ dirichletDomain P w := by
    obtain ⟨δ,hδi,hδf,hδD⟩ := dirichlet_circle_arc_neighbor_frontier_path
      P w R hR u hu (E.symm (xs n)).val (E.symm (b (xs n))).val (harc (xs n))
    let δ' : Path (x n) (y n) := δ.cast (heval (xs n)).symm (heval (b (xs n))).symm
    refine ⟨δ',hδi,hδf,?_⟩
    change range δ \ {x n,y n} ⊆ dirichletDomain P w
    simpa only [heval] using hδD
  let γ : ∀ n, Path (x n) (y n) := fun n => (hpaths n).choose
  let t : ℕ → H := fun n => (hpair (b (xs n))).choose
  have ht (n : ℕ) : t n • y n = x (n + 1) := by
    have hh := (hpair (b (xs n))).choose_spec.2
    change t n • y n = _ at hh
    simpa only [x,xs,pow_succ',Equiv.Perm.mul_apply] using hh
  have hcycle : x N = x 0 := by
    simp only [x,xs,hperiod,pow_zero,Equiv.Perm.one_apply]
  have hxzero : xs 0 = x₀ := by simp only [xs,pow_zero,Equiv.Perm.one_apply]
  have hxS : x 0 ∈ frontier (fuchsianOrbitBallUnion P w R) := by
    have hh := (hpaths 0).choose_spec.2.1 (show γ 0 0 ∈ range (γ 0) from mem_range_self 0)
    simpa only [Path.source] using hh
  have hS (k : H) (v : P.domain.carrier)
      (hv : v ∈ frontier (fuchsianOrbitBallUnion P w R)) :
      k • v ∈ frontier (fuchsianOrbitBallUnion P w R) := by
    have hh : k • v ∈ k • frontier (fuchsianOrbitBallUnion P w R) := smul_mem_smul_set hv
    rwa [fuchsianOrbitBallUnion_frontier_invariant] at hh
  let k := pathDevelopmentTransform t N
  let Γ' := equivariantCycleDevelopment x y t ht γ N hcycle
  have hΓ' : range Γ' ⊆ frontier (fuchsianOrbitBallUnion P w R) :=
    equivariantCycleDevelopment_range_subset x y t ht γ N hcycle _ hS hxS
      (fun n => (hpaths n).choose_spec.2.1)
  let Γ : Path x₀.val (k • x₀.val) := Γ'.cast
    (congrArg Subtype.val hxzero.symm)
    (congrArg (fun z => k • z.val) hxzero.symm)
  let δ : Path x₀.val (b x₀).val := (γ 0).cast
    (congrArg Subtype.val hxzero.symm)
    (congrArg (fun z => (b z).val) hxzero.symm)
  have hδi : Function.Injective δ := (hpaths 0).choose_spec.1
  have hδΓ : range δ ⊆ range Γ :=
    equivariantPathDevelopment_firstArc_subset x y t ht γ N hN
  refine ⟨k,Γ,hΓ',δ,hδi,hδΓ,?_⟩
  have hh := (hpaths 0).choose_spec.2.2
  change range (γ 0) \ {x 0,y 0} ⊆ _ at hh
  change range (γ 0) \ {x₀.val,(b x₀).val} ⊆ dirichletDomain P w
  simpa only [x,y,hxzero] using hh

/-- Under actual finite generation, cofinally large connected whole-orbit neighborhoods
have genuine developed frontier paths through every actual Dirichlet circle cut. Each
contains a genuine nonconstant injective component arc inside the original polygon.
No injectivity of the entire developed path or finite-end conclusion is asserted. -/
theorem finitelyGenerated_developed_frontier_paths
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (hFG :
      H.FG)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (g : H) (hg : g ≠ 1) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧
      IsOpen (fuchsianOrbitBallUnion P w R) ∧ IsConnected (fuchsianOrbitBallUnion P w R) ∧
      (dirichletCircleCuts P w R).Finite ∧
      ∀ x : dirichletCircleCuts P w R, ∃ k : H, ∃ Γ : Path x.val (k • x.val),
        range Γ ⊆ frontier (fuchsianOrbitBallUnion P w R) ∧
        ∃ q : P.domain.carrier, q ≠ x.val ∧ ∃ δ : Path x.val q,
          Function.Injective δ ∧ range δ ⊆ range Γ ∧
          range δ \ {x.val,q} ⊆ dirichletDomain P w := by
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  have hz : g • w ∉ closure (dirichletDomain P w) := fun hh =>
    disjoint_left.mp (hD.locallyFinite.fundamental.disjoint_image_closure hg)
      (smul_mem_smul_set (dirichletDomain_center_mem P w hw)) hh
  obtain ⟨R,hbig,hR,hOpen,hConn,hFin,hFinU,E,hE,a,b,_hai,_haNe,hpair,_hbi,hbNe,harc,N,hN,hperiod⟩ :=
    finitelyGenerated_dirichlet_circle_gluing_data P hFG w hw g hg
      (max R₀ (P.hyperbolicDist w (g • w)))
  obtain ⟨z,hzR,hzD⟩ := fuchsian_polygon_large_circle_exterior hD w (g • w)
    (dirichletDomain_center_mem P w hw) hz R ((le_max_right _ _).trans_lt hbig)
  let e := fuchsianMetricCircleHomeomorph P w R hR
  let f : Circle → P.domain.carrier := fun z => (e z).val
  let U := f ⁻¹' dirichletDomain P w
  let u := e.symm ⟨z,hzR⟩
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hfu : f u = z := congrArg Subtype.val (e.apply_symm_apply ⟨z,hzR⟩)
  have hu : u ∉ closure U := by
    intro hh
    exact hzD (hfu ▸ hf.closure_preimage_subset (dirichletDomain P w) hh)
  refine ⟨R,(le_max_left _ _).trans_lt hbig,hR,hOpen,hConn,hFin,?_⟩
  intro x
  obtain ⟨k,Γ,hΓ,δ,hδi,hδΓ,hδD⟩ := dirichlet_circle_pairings_develop_actual_paths P w R hR
    u hu E hE a b (fun x => (hpair x).exists) harc N hN hperiod x
  refine ⟨k,Γ,hΓ,(b x).val,?_,δ,hδi,hδΓ,hδD⟩
  intro he
  exact hbNe x (Subtype.ext he)

end LowDimensionalTopology.Geometry.Fuchsian
