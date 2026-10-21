module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletFiniteBoundaryCycles
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.EquivariantPath
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Pointwise unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- A compact set meets only finitely many genuine integer translates of the
given compact path when the translating element has infinite order. -/
theorem equivariantPathExtension_finite_intersecting_blocks
    {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ProperlyDiscontinuousSMul G X]
    (g : G) (hg : Function.Injective (fun n : ℤ => g^n))
    {x : X} (γ : Path x (g • x)) {K : Set X} (hK : IsCompact K) :
    {n : ℤ | ((fun y : X => g^n • y) '' range γ ∩ K).Nonempty}.Finite := by
  have hγ : IsCompact (range γ) := isCompact_range γ.continuous
  have hfin : {a : G | ((fun y : X => a • y) '' range γ ∩ K).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) hγ hK
  change ((fun n : ℤ => g^n) ⁻¹'
    {a : G | ((fun y : X => a • y) '' range γ ∩ K).Nonempty}).Finite
  exact hfin.preimage hg.injOn

/-- The actual real developed curve has compact inverse images of compact sets,
without assuming injectivity of its parametrization. -/
theorem equivariantPathExtension_isCompact_preimage
    {G X : Type*} [Group G] [TopologicalSpace X] [T2Space X]
    [MulAction G X] [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    (g : G) (hg : Function.Injective (fun n : ℤ => g^n))
    {x : X} (γ : Path x (g • x)) {K : Set X} (hK : IsCompact K) :
    IsCompact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ) ⁻¹' K) := by
  let S : Set ℤ := {n | ((fun y : X => g^n • y) '' range γ ∩ K).Nonempty}
  have hS : S.Finite := equivariantPathExtension_finite_intersecting_blocks g hg γ hK
  have hUnion : IsCompact (⋃ n ∈ S, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.pathExtensionInterval
    n) :=
    hS.isCompact_biUnion (fun n _ => isCompact_Icc)
  apply hUnion.of_isClosed_subset
    (hK.isClosed.preimage
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.continuous_equivariantPathExtension g γ))
  intro t ht
  let n := ⌊t⌋
  have htn : t ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.pathExtensionInterval n :=
    ⟨Int.floor_le t,(Int.lt_floor_add_one t).le⟩
  have hmem : γ.extend (t-(n:ℝ)) ∈ range γ := by
    rw [←γ.extend_range]
    exact mem_range_self _
  have hn : n ∈ S := by
    refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ t,?_,ht⟩
    exact ⟨γ.extend (t-(n:ℝ)),hmem,
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_on_interval g γ n
        htn).symm⟩
  exact mem_iUnion₂.mpr ⟨n,hn,htn⟩

/-- Proper discontinuity gives genuine properness of the entire actual real
developed curve whenever the translating group element has infinite order. -/
theorem equivariantPathExtension_isProperMap
    {G X : Type*} [Group G] [TopologicalSpace X] [T2Space X]
    [CompactlyCoherentSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X]
    (g : G) (hg : Function.Injective (fun n : ℤ => g^n))
    {x : X} (γ : Path x (g • x)) : IsProperMap (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ) := by
  exact isProperMap_iff_isCompact_preimage.mpr
    ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.continuous_equivariantPathExtension g γ,
      fun _ hK => equivariantPathExtension_isCompact_preimage g hg γ hK⟩

/-- An injective such parametrization is a genuine closed embedding of the real
line, rather than merely a continuous equivariant curve. -/
theorem equivariantPathExtension_isClosedEmbedding
    {G X : Type*} [Group G] [TopologicalSpace X] [T2Space X]
    [CompactlyCoherentSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X]
    (g : G) (hg : Function.Injective (fun n : ℤ => g^n))
    {x : X} (γ : Path x (g • x))
    (hγ : Function.Injective (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g
      γ)) :
    IsClosedEmbedding (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ) := by
  exact .of_continuous_injective_isClosedMap
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.continuous_equivariantPathExtension g γ) hγ
    (equivariantPathExtension_isProperMap g hg γ).isClosedMap

/-- The actual full real-parameter extension respects every integer translation,
including negative ones. -/
theorem equivariantPathExtension_add_int
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (g : G) {x : X} (γ : Path x (g • x)) (t : ℝ) (n : ℤ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ (t+(n:ℝ)) = g^n • _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ t := by
  let m := ⌊t⌋
  have ht : t ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.pathExtensionInterval m :=
    ⟨Int.floor_le t,(Int.lt_floor_add_one t).le⟩
  have ht' : t+(n:ℝ) ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.pathExtensionInterval (m+n) := by
    change ((m+n:ℤ):ℝ) ≤ t+(n:ℝ) ∧ t+(n:ℝ) ≤ ((m+n:ℤ):ℝ)+1
    push_cast
    constructor <;> linarith [ht.1,ht.2]
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_on_interval g γ (m+n) ht',
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_on_interval g γ m ht]
  have harg : t+(n:ℝ)-((m+n:ℤ):ℝ) = t-(m:ℝ) := by push_cast; ring
  rw [harg,show m+n = n+m by omega,zpow_add,mul_smul]

/-- Separation of genuine nonnegative compact blocks, together with the original
path's injectivity, already implies injectivity on the nonnegative real axis. -/
theorem equivariantPathExtension_injOn_nonnegative
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (g : G) {x : X} (γ : Path x (g • x)) (hγ : Function.Injective γ)
    (hsep : ∀ n m : ℕ, n < m →
      (g^n • range γ) ∩ (g^m • range γ) ⊆ {g^(n+1) • x}) :
    Set.InjOn (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ) (Ici (0:ℝ)) := by
  have hfloor (t : ℝ) (ht : 0 ≤ t) :
      ∃ u : I, (u:ℝ) < 1 ∧ t = (⌊t⌋₊:ℝ)+(u:ℝ) ∧
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ t = g^⌊t⌋₊ • γ u := by
    let n := ⌊t⌋₊
    have hn : (n:ℝ) ≤ t := Nat.floor_le ht
    have hn' : t < (n:ℝ)+1 := Nat.lt_floor_add_one t
    let u : I := ⟨t-(n:ℝ),by linarith,by linarith⟩
    refine ⟨u,by dsimp [u]; linarith,by dsimp [u]; ring,?_⟩
    have hi : t ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.pathExtensionInterval (n:ℤ) := by
      change (n:ℝ) ≤ t ∧ t ≤ (n:ℝ)+1
      exact ⟨hn,hn'.le⟩
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_on_interval g γ (n:ℤ) hi]
    simpa only [Int.cast_natCast,zpow_natCast] using
      congrArg (fun y : X => g^n • y) (Path.extend_extends' γ u)
  intro s hs t ht he
  obtain ⟨u,hu,hsu,hFu⟩ := hfloor s hs
  obtain ⟨v,hv,htv,hFv⟩ := hfloor t ht
  rw [hFu,hFv] at he
  have hne (n m : ℕ) (hnm : n < m) (u v : I) (hu : (u:ℝ) < 1)
      (he : g^n • γ u = g^m • γ v) : False := by
    have hp : g^n • γ u ∈ (g^n • range γ) ∩ (g^m • range γ) :=
      ⟨smul_mem_smul_set (mem_range_self u),he.symm ▸ smul_mem_smul_set (mem_range_self v)⟩
    have hend := mem_singleton_iff.mp (hsep n m hnm hp)
    rw [pow_succ,mul_smul] at hend
    have hend' : g^n • γ u = g^n • γ 1 :=
      hend.trans (congrArg (fun y : X => g^n • y) γ.target.symm)
    have huone := hγ (MulAction.injective (g^n) hend')
    have heval := congrArg (fun z : I => (z:ℝ)) huone
    exact (ne_of_lt hu) heval
  have hnm : ⌊s⌋₊ = ⌊t⌋₊ := by
    rcases lt_trichotomy ⌊s⌋₊ ⌊t⌋₊ with h | h | h
    · exact False.elim (hne _ _ h u v hu he)
    · exact h
    · exact False.elim (hne _ _ h v u hv he.symm)
  rw [hnm] at he
  have huv := congrArg (fun z : I => (z:ℝ)) (hγ (MulAction.injective _ he))
  rw [hsu,htv,hnm,huv]

/-- The entire genuine real curve is injective once its original path and its
genuine nonnegative compact blocks have the stated actual geometric separation. -/
theorem equivariantPathExtension_injective_of_block_separation
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (g : G) {x : X} (γ : Path x (g • x)) (hγ : Function.Injective γ)
    (hsep : ∀ n m : ℕ, n < m →
      (g^n • range γ) ∩ (g^m • range γ) ⊆ {g^(n+1) • x}) :
    Function.Injective (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ) := by
  intro s t he
  obtain ⟨N,hN⟩ := exists_nat_gt (max (-s) (-t))
  have hs : 0 ≤ s+(N:ℝ) := by linarith [le_max_left (-s) (-t)]
  have ht : 0 ≤ t+(N:ℝ) := by linarith [le_max_right (-s) (-t)]
  have he' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ (s+(N:ℝ)) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension g γ (t+(N:ℝ)) := by
    have h := congrArg (fun y : X => g^(N:ℤ) • y) he
    simpa only [←equivariantPathExtension_add_int,Int.cast_natCast] using h
  have hh := equivariantPathExtension_injOn_nonnegative g γ hγ hsep hs ht he'
  linarith



/-- A true return of the projected cut determines the genuine accumulated tile
at every later whole block; the full state need not itself return. -/
theorem endpointSkewPermutation_pow_blocks {G X : Type*} [Group G]
    (r : Equiv.Perm X) (c : X → G) (L : ℕ) (x : X) (k : G)
    (hL : ((endpointSkewPermutation r c)^L) (1,x) = (k,x)) (n : ℕ) :
    ((endpointSkewPermutation r c)^(L*n)) (1,x) = (k^n,x) := by
  induction n with
  | zero => simp only [Nat.mul_zero,pow_zero,Equiv.Perm.one_apply]
  | succ n ih =>
      rw [Nat.mul_succ,pow_add,Equiv.Perm.mul_apply,hL]
      have hk : (k,x) = (k*1,x) := by simp
      rw [hk,endpointSkewPermutation_pow_left_mul,ih]
      simp only [pow_succ']

/-- Every actual arc state in a later block is the same original arc state
translated by the genuine accumulated block element. -/
theorem endpointSkewPermutation_pow_block_add {G X : Type*} [Group G]
    (r : Equiv.Perm X) (c : X → G) (L : ℕ) (x : X) (k : G)
    (hL : ((endpointSkewPermutation r c)^L) (1,x) = (k,x)) (n i : ℕ) :
    ((endpointSkewPermutation r c)^(L*n+i)) (1,x) =
      (k^n*(((endpointSkewPermutation r c)^i) (1,x)).1,
        (((endpointSkewPermutation r c)^i) (1,x)).2) := by
  rw [add_comm (L*n) i,pow_add,Equiv.Perm.mul_apply,
    endpointSkewPermutation_pow_blocks r c L x k hL n]
  have hk : (k^n,x) = (k^n*1,x) := by simp
  rw [hk,endpointSkewPermutation_pow_left_mul]

open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- The genuine finite cut permutation returns some positive number of steps
later, with its exact original accumulated tile retained in the full state. -/
theorem exists_cut_return_block (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    ∃ L : ℕ, 0 < L ∧ ∃ k : H, d.state hw x L = (k,x) := by
  let : Finite (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :=
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts_finite P w hw d.radius).to_subtype
  obtain ⟨L,hL,hpow⟩ :=
    (isOfFinOrder_of_finite (d.pairing hw*d.arcReversal hw)).exists_pow_eq_one
  refine ⟨L,hL,(d.state hw x L).1,?_⟩
  apply Prod.ext
  · rfl
  · rw [d.state_snd,hpow]
    rfl

/-- If the true full state is aperiodic, each positive cut-return block has an
actual infinite-order original group element as its accumulated tile. -/
theorem cut_return_block_zpow_injective (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hzero : d.endpointPeriod hw
      x = 0)
    (L : ℕ) (hL : 0 < L) (k : H) (hstate : d.state hw x L = (k,x)) :
    Function.Injective (fun n : ℤ => k^n) := by
  apply injective_zpow_iff_not_isOfFinOrder.mpr
  intro hk
  obtain ⟨n,hn,hpow⟩ := hk.exists_pow_eq_one
  have he : d.state hw x (L*n) = d.state hw x 0 := by
    change ((d.endpointStep hw)^(L*n)) (1,x) = (1,x)
    change ((_root_.LowDimensionalTopology.Geometry.Fuchsian.endpointSkewPermutation _ _)^(L*n)) (1,x) = (1,x)
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.endpointSkewPermutation_pow_blocks _ _ L x k hstate n,hpow]
  have hz := d.state_injective_of_period_zero hw x hzero he
  exact (Nat.mul_pos hL hn).ne' hz

/-- Before any genuine full-state return, two compact developed arcs with
different positions can meet only at the shared endpoint of consecutive arcs. -/
theorem aperiodic_developedClosedArc_intersection (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hzero : d.endpointPeriod hw
      x = 0)
    (i j : ℕ) (hij : i < j) {p : P.domain.carrier}
    (hp : p ∈ d.developedClosedArc hw x i ∩ d.developedClosedArc hw x j) :
    i+1 = j ∧ p = d.vertex hw x j := by
  have hinj := d.state_injective_of_period_zero hw x hzero
  by_cases hstep : i+1 = j
  · subst j
    have he := d.developedClosedArc_adjacent_intersection hw x i
      (fun h => (by omega : i ≠ i+1) (hinj h))
      (fun h => (by omega : i ≠ i+2) (hinj h))
    exact ⟨rfl,mem_singleton_iff.mp (he ▸ hp)⟩
  · have hd := d.developedClosedArc_disjoint_of_endpoint_states hw x i j
      (fun h => (Nat.ne_of_lt hij) (hinj h))
      (fun h => (by omega : i ≠ j+1) (hinj h))
      (fun h => hstep (hinj h))
      (fun h => (by omega : i+1 ≠ j+1) (hinj h))
    exact False.elim (disjoint_left.mp hd hp.1 hp.2)

/-- A genuine positive cut-return block in the aperiodic branch admits a true
injective path from the initial original point to its genuine accumulated tile
translate, with its exact original finite arc image. -/
theorem aperiodic_cut_return_block_path (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hzero : d.endpointPeriod hw
      x = 0)
    (L : ℕ) (hL : 0 < L) (k : H) (hstate : d.state hw x L = (k,x)) :
    ∃ γ : Path x.val (k • x.val), Function.Injective γ ∧
      range γ = ⋃ i ∈ Iio L, d.developedClosedArc hw x i ∧
      range γ ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
  have hL' : L-1+1 = L := Nat.sub_add_cancel hL
  obtain ⟨γ,hγ,hγrange,hγfront⟩ :=
    d.exists_injective_developed_path_of_period_zero hw x hzero (L-1)
  have ht : k • x.val = d.vertex hw x (L-1+1) := by
    rw [hL',vertex,hstate]
  refine ⟨γ.cast rfl ht,?_,?_,?_⟩
  · exact hγ
  · change range γ = _
    rw [hγrange]
    have hset : Iic (L-1) = Iio L := by
      ext i
      simp only [mem_Iic,mem_Iio]
      omega
    rw [hset]
  · exact hγfront

/-- The true full state of every later block is an exact original tile translate
of the initial block state, including its original cut. -/
theorem cut_return_block_state_add (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (L : ℕ) (k : H)
    (hstate : d.state hw x L = (k,x)) (n i : ℕ) :
    d.state hw x (L*n+i) = (k^n*(d.state hw x i).1,(d.state hw x i).2) := by
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.endpointSkewPermutation_pow_block_add _ _ L x k hstate n i

/-- Actual compact developed arcs repeat by the genuine accumulated block tile,
without replacing the original action by an abstract model. -/
theorem cut_return_block_closedArc_add (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (L : ℕ) (k : H)
    (hstate : d.state hw x L = (k,x)) (n i : ℕ) :
    d.developedClosedArc hw x (L*n+i) = k^n • d.developedClosedArc hw x i := by
  rw [developedClosedArc,d.cut_return_block_state_add hw x L k hstate n i]
  change (k^n*(d.state hw x i).1) • closure (d.originalArc hw (d.state hw x i).2) = _
  exact mul_smul _ _ _

/-- The actual endpoints between whole blocks are exactly the genuine original
orbit points of the accumulated block element. -/
theorem cut_return_block_vertex (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (L : ℕ) (k : H)
    (hstate : d.state hw x L = (k,x)) (n : ℕ) :
    d.vertex hw x (L*n) = k^n • x.val := by
  have he := d.cut_return_block_state_add hw x L k hstate n 0
  have hz : d.state hw x 0 = (1,x) := rfl
  simp only [Nat.add_zero,hz,mul_one] at he
  change (d.state hw x (L*n)).1 • (d.state hw x (L*n)).2.val = _
  rw [he]

/-- Two distinct nonnegative whole blocks of the genuine aperiodic developed
curve meet, if at all, only at the terminal point of the earlier block. -/
theorem aperiodic_cut_return_block_intersection (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter
  P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hzero : d.endpointPeriod hw
      x = 0)
    (L : ℕ) (k : H) (hstate : d.state hw x L = (k,x))
    (γ : Path x.val (k • x.val))
    (hγ : range γ = ⋃ i ∈ Iio L, d.developedClosedArc hw x i)
    (n m : ℕ) (hnm : n < m) :
    (k^n • range γ) ∩ (k^m • range γ) ⊆ {k^(n+1) • x.val} := by
  intro p hp
  simp only [hγ,smul_set_iUnion₂] at hp
  obtain ⟨i,hpi⟩ := mem_iUnion.mp hp.1
  obtain ⟨hi,hpi⟩ := mem_iUnion.mp hpi
  obtain ⟨j,hpj⟩ := mem_iUnion.mp hp.2
  obtain ⟨hj,hpj⟩ := mem_iUnion.mp hpj
  rw [←d.cut_return_block_closedArc_add hw x L k hstate n i] at hpi
  rw [←d.cut_return_block_closedArc_add hw x L k hstate m j] at hpj
  have hi' : i < L := mem_Iio.mp hi
  have hj' : j < L := mem_Iio.mp hj
  have hbound : L*n+i+1 ≤ L*(n+1) := by rw [Nat.mul_succ]; omega
  have hstep : L*(n+1) ≤ L*m := Nat.mul_le_mul_left L hnm
  have hij : L*n+i < L*m+j := by omega
  obtain ⟨hijEq,hpEq⟩ := d.aperiodic_developedClosedArc_intersection hw x hzero
    (L*n+i) (L*m+j) hij ⟨hpi,hpj⟩
  have heq : L*m+j = L*(n+1) := by omega
  rw [heq,d.cut_return_block_vertex hw x L k hstate (n+1)] at hpEq
  exact mem_singleton_iff.mpr hpEq

/-- The genuine aperiodic branch of the original boundary construction is an
actual properly embedded real line, invariant under an actual infinite-order
original group element, with its exact whole-block arc image. -/
theorem aperiodic_exists_proper_embedded_frontier_curve (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hzero : d.endpointPeriod hw
      x = 0) :
    ∃ L : ℕ, 0 < L ∧ ∃ k : H, ∃ γ : Path x.val (k • x.val),
      Function.Injective (fun n : ℤ => k^n) ∧ Function.Injective γ ∧
      range γ = ⋃ i ∈ Iio L, d.developedClosedArc hw x i ∧
      IsProperMap (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ) ∧
      IsClosedEmbedding (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ) ∧
      range (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ) =
        ⋃ n : ℤ, k^n • (⋃ i ∈ Iio L, d.developedClosedArc hw x i) ∧
      range (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ) ⊆
        frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  let : ProperlyDiscontinuousSMul H P.domain.carrier :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_properlyDiscontinuous P.domain P.discontinuous
  obtain ⟨L,hL,k,hstate⟩ := d.exists_cut_return_block hw x
  have hk := d.cut_return_block_zpow_injective hw x hzero L hL k hstate
  obtain ⟨γ,hγ,hγrange,hγfront⟩ :=
    d.aperiodic_cut_return_block_path hw x hzero L hL k hstate
  have hsep := d.aperiodic_cut_return_block_intersection hw x hzero L k hstate γ hγrange
  have hproper := _root_.LowDimensionalTopology.Geometry.Fuchsian.equivariantPathExtension_isProperMap k hk γ
  have hembed := _root_.LowDimensionalTopology.Geometry.Fuchsian.equivariantPathExtension_isClosedEmbedding k hk γ
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.equivariantPathExtension_injective_of_block_separation k γ hγ hsep)
  refine ⟨L,hL,k,γ,hk,hγ,hγrange,hproper,hembed,?_,?_⟩
  · rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_range,hγrange]
  · apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_range_subset k γ _ _ hγfront
    intro n z hz
    have hh : k^n • z ∈ k^n • frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w
      d.radius) :=
      smul_mem_smul_set hz
    rwa [_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion_frontier_invariant] at hh

end RegularDirichletCircleData

/-- Genuine finite generation gives cofinally large original regular circles
whose every actual boundary cut lies on either a genuine embedded circle or a
genuine properly embedded real line, entirely on the literal whole-orbit
neighborhood frontier. No separation or finite-end theorem is assumed here. -/
theorem finitelyGenerated_embedded_frontier_curve_dichotomy
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (hFG :
      H.FG)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    (hw : IsDirichletCenter P w) (R₀ : ℝ) :
    ∃ d : RegularDirichletCircleData P w, R₀ < d.radius ∧
      ∀ x : dirichletCircleCuts P w d.radius,
        (∃ J : Circle → P.domain.carrier, Continuous J ∧ Function.Injective J ∧
          x.val ∈ range J ∧ range J ⊆ frontier (fuchsianOrbitBallUnion P w d.radius)) ∨
        (∃ k : H, ∃ F : ℝ → P.domain.carrier,
          Function.Injective (fun n : ℤ => k^n) ∧ IsProperMap F ∧ IsClosedEmbedding F ∧
          F 0 = x.val ∧ (∀ t : ℝ, F (t+1) = k • F t) ∧
          range F ⊆ frontier (fuchsianOrbitBallUnion P w d.radius)) := by
  obtain ⟨g,hg,hlox⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.nonElementary_exists_loxodromic H hNE
  have hgne : (⟨g,hg⟩:H) ≠ 1 := fun h => hlox.1 (congrArg Subtype.val h)
  obtain ⟨d,hd⟩ := finitelyGenerated_regular_dirichlet_circle_data P hFG w hw ⟨g,hg⟩ hgne R₀
  refine ⟨d,hd,?_⟩
  intro x
  by_cases hzero : d.endpointPeriod hw x = 0
  · right
    obtain ⟨L,_hL,k,γ,hk,_hγ,_hγrange,hproper,hembed,_hrange,hfront⟩ :=
      d.aperiodic_exists_proper_embedded_frontier_curve hw x hzero
    refine ⟨k,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k
      γ,hk,hproper,hembed,?_,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_add_one k γ,hfront⟩
    simpa only [Int.cast_zero,zpow_zero,one_smul] using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_int k γ 0
  · left
    have hpos : 0 < d.endpointPeriod hw x := Nat.pos_of_ne_zero hzero
    obtain ⟨J,hJ,hJinj,hJrange,hfront⟩ := d.finite_period_exists_jordan_curve hw x hpos
    refine ⟨J,hJ,hJinj,?_,hfront⟩
    rw [hJrange]
    have hx : x.val ∈ range (d.developedPath hw x 0) :=
      ⟨0,(d.developedPath hw x 0).source⟩
    rw [(d.developedPath_spec hw x 0).2] at hx
    exact mem_iUnion₂.mpr ⟨0,hpos,hx⟩

end LowDimensionalTopology.Geometry.Fuchsian
