/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Trace.HalfTurnTraces
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.CollinearHalfTurns
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The even pair subgroup of three actual involutions is normalized by the first involution. -/
theorem three_involutions_pair_conjugation {G:Type*} [Group G]
    (a b c:G) (ha:a*a=1) (hb:b*b=1) (hc:c*c=1)
    (x:G) (hx:x∈Subgroup.closure ({b*a,c*a}:Set G)) :
    a*x*a∈Subgroup.closure ({b*a,c*a}:Set G) := by
  let H:=Subgroup.closure ({b*a,c*a}:Set G)
  have haa (y:G):a*(a*y)=y:=by rw [←mul_assoc,ha,one_mul]
  have hai:a⁻¹=a:=inv_eq_of_mul_eq_one_left ha
  have hbi:b⁻¹=b:=inv_eq_of_mul_eq_one_left hb
  have hci:c⁻¹=c:=inv_eq_of_mul_eq_one_left hc
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl|rfl
    · simpa only [mul_inv_rev,hai,hbi,mul_assoc,ha,mul_one] using
        H.inv_mem (Subgroup.subset_closure (by simp:b*a∈({b*a,c*a}:Set G)))
    · simpa only [mul_inv_rev,hai,hci,mul_assoc,ha,mul_one] using
        H.inv_mem (Subgroup.subset_closure (by simp:c*a∈({b*a,c*a}:Set G)))
  | one => simpa only [mul_one,ha] using H.one_mem
  | mul x y _ _ hx hy =>
    have he:a*(x*y)*a=(a*x*a)*(a*y*a):=by simp only [mul_assoc,haa]
    rw [he]
    exact H.mul_mem hx hy
  | inv x _ hx =>
    have he:a*x⁻¹*a=(a*x*a)⁻¹:=by simp only [mul_inv_rev,hai,mul_assoc]
    rw [he]
    exact H.inv_mem hx

/-- Every word in three involutions is even or belongs to the one odd coset. -/
theorem three_involutions_pair_cosets {G:Type*} [Group G]
    (a b c:G) (ha:a*a=1) (hb:b*b=1) (hc:c*c=1)
    (x:G) (hx:x∈Subgroup.closure ({a,b,c}:Set G)) :
    x∈Subgroup.closure ({b*a,c*a}:Set G) ∨
      a*x∈Subgroup.closure ({b*a,c*a}:Set G) := by
  let H:=Subgroup.closure ({b*a,c*a}:Set G)
  have haa (y:G):a*(a*y)=y:=by rw [←mul_assoc,ha,one_mul]
  have hai:a⁻¹=a:=inv_eq_of_mul_eq_one_left ha
  have hba:b*a∈H:=Subgroup.subset_closure (by simp)
  have hca:c*a∈H:=Subgroup.subset_closure (by simp)
  have hab:a*b∈H:=by
    have hh:=three_involutions_pair_conjugation a b c ha hb hc (b*a) hba
    simpa only [mul_assoc,ha,mul_one] using hh
  have hac:a*c∈H:=by
    have hh:=three_involutions_pair_conjugation a b c ha hb hc (c*a) hca
    simpa only [mul_assoc,ha,mul_one] using hh
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl|rfl|rfl
    · exact Or.inr (ha ▸ H.one_mem)
    · exact Or.inr hab
    · exact Or.inr hac
  | one => exact Or.inl H.one_mem
  | mul x y _ _ hx hy =>
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact Or.inl (H.mul_mem hx hy)
    · apply Or.inr
      have hh:=H.mul_mem (three_involutions_pair_conjugation a b c ha hb hc x hx) hy
      simpa only [mul_assoc,haa] using hh
    · exact Or.inr (by simpa only [mul_assoc] using H.mul_mem hx hy)
    · apply Or.inl
      have hh:=H.mul_mem (three_involutions_pair_conjugation a b c ha hb hc (a*x) hx) hy
      simpa only [mul_assoc,haa] using hh
  | inv x _ hx =>
    rcases hx with hx|hx
    · exact Or.inl (H.inv_mem hx)
    · apply Or.inr
      have hh:=H.inv_mem (three_involutions_pair_conjugation a b c ha hb hc (a*x) hx)
      simpa only [mul_inv_rev,hai,mul_assoc,haa,mul_one] using hh

/-- The true pair subgroup has index one or two in the three-involution group. -/
theorem three_involutions_pair_relIndex {G:Type*} [Group G]
    (a b c:G) (ha:a*a=1) (hb:b*b=1) (hc:c*c=1) :
    let H:=Subgroup.closure ({b*a,c*a}:Set G)
    let K:=Subgroup.closure ({a,b,c}:Set G)
    H≤K ∧ (H.relIndex K=1 ∨ H.relIndex K=2) := by
  dsimp
  have hle:Subgroup.closure ({b*a,c*a}:Set G)≤Subgroup.closure ({a,b,c}:Set G):=by
    apply (Subgroup.closure_le _).2
    intro x hx
    rcases hx with rfl|rfl
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  refine ⟨hle,?_⟩
  have hd:(Subgroup.closure ({b*a,c*a}:Set G)).relIndex
      (Subgroup.closure ({a,b,c}:Set G))∣2:=by
    apply Subgroup.relIndex_dvd_two_iff'.mpr
    refine ⟨a,Subgroup.subset_closure (by simp),?_⟩
    intro x hx
    exact (three_involutions_pair_cosets a b c ha hb hc x hx).symm
  exact (Nat.dvd_prime Nat.prime_two).mp hd


/-- A finite-index three-involution extension of the actual discrete pair remains discrete. -/
theorem three_involutions_pair_discrete (a b c:Mobius.complexMobiusGroup)
    (ha:a*a=1) (hb:b*b=1) (hc:c*c=1)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({b*a,c*a}:Set Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({a,b,c}:Set Mobius.complexMobiusGroup)) := by
  obtain ⟨hle,hi⟩:=three_involutions_pair_relIndex a b c ha hb hc
  let crossingEvenFiniteIndex : (Subgroup.closure ({b*a,c*a}:Set Mobius.complexMobiusGroup)).IsFiniteRelIndex
      (Subgroup.closure ({a,b,c}:Set Mobius.complexMobiusGroup)):=⟨by rcases hi with h|h <;> omega⟩
  exact (Subgroup.discreteTopology_iff_of_isFiniteRelIndex hle).mp hd

/-- The canonical actual point half-turns realize every actual two-center factorization. -/
theorem pointHalfTurns_factorization (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (u v:ℍ) (h:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HasHalfTurnFactorization A u v) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL v)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u) := by
  obtain ⟨B,C,hB,hC,he⟩:=h
  rw [hB.unique (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at u),
    hC.unique (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at v)] at he
  exact he

/-- The actual intersection and half-translation points yield a discrete three-half-turn extension
of the full original hyperbolic pair subgroup, with relative index one or two. -/
theorem crossingAxis_halfturn_extension (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup))) :
    ∃v w:ℍ,
      v∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier ∧ w∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)=2*dist u v ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=2*dist u w ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL v)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u) ∧
      let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)
      let K:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL v),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:Set Mobius.complexMobiusGroup)
      H≤K ∧ (H.relIndex K=1 ∨ H.relIndex K=2) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K := by
  obtain ⟨v,⟨hvA,hfactA,hlenA⟩,_⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_hyperbolic_halfturn_factor A hA htA u huA
  obtain ⟨w,⟨hwB,hfactB,hlenB⟩,_⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_hyperbolic_halfturn_factor B hB htB u huB
  have heA:=pointHalfTurns_factorization A u v hfactA
  have heB:=pointHalfTurns_factorization B u w hfactB
  have hi (z:ℍ):_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL z)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL z)=1:=by
    have hh:=pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL z))
    rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at z).1] at hh
    simpa only [pow_two] using hh
  have hindex:=three_involutions_pair_relIndex _ _ _ (hi u) (hi v) (hi w)
  have hdiscrete:=three_involutions_pair_discrete _ _ _ (hi u) (hi v) (hi w)
  rw [←heA,←heB] at hindex hdiscrete
  exact ⟨v,w,hvA,hwB,hlenA,hlenB,heA,heB,hindex.1,hindex.2,hdiscrete hd⟩


/-- A non-elementary crossing pair produces a genuine noncollinear triangle of the three centers,
with its original half-translation side lengths and actual finite-index discrete extension. -/
theorem crossingAxis_halfturn_triangle (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)))
    (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup))) :
    ∃T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle,T.a=u ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.b)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.a) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.c)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.a) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)=2*T.lengthC ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=2*T.lengthB ∧
      let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)
      let K:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.a),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.b),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.c)}:Set Mobius.complexMobiusGroup)
      H≤K ∧ (H.relIndex K=1 ∨ H.relIndex K=2) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K := by
  obtain ⟨v,w,_hv,_hw,hlenA,hlenB,heA,heB,hle,hi,hdK⟩:=
    crossingAxis_halfturn_extension A B hA hB htA htB u huA huB hd
  have huv:u≠v:=by
    intro he
    apply hA
    rw [heA,he]
    have hh:=pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL v))
    rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at v).1] at hh
    simpa only [pow_two] using hh
  have hNEK:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL u),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL v),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:Set Mobius.complexMobiusGroup)):=
    fun h=>hNE (h.mono hle)
  have hnc:¬∃L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,u∈L.carrier ∧ v∈L.carrier ∧ w∈L.carrier:=by
    rintro ⟨L,hLu,hLv,hLw⟩
    exact hNEK (collinear_halfTurns_elementary L u v w huv hLu hLv hLw _ _ _
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at u) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at v) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at w))
  let T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle:=⟨u,v,w,hnc⟩
  refine ⟨T,rfl,heA,heB,hlenA,?_,hle,hi,hdK,hNEK⟩
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle.lengthB,dist_comm,T] using hlenB

/-- The exact crossing-axis product is the genuine invariant of the actual three-center triangle. -/
theorem crossingAxis_halfturn_invariant (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (a b:ℝ)
    (ha:a=2*T.lengthC) (hb:b=2*T.lengthB) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T=Real.sinh (a/2)*Real.sinh (b/2)*Real.sin T.alpha := by
  have ha':a/2=T.lengthC:=by linarith only [ha]
  have hb':b/2=T.lengthB:=by linarith only [hb]
  rw [ha',hb',_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant]
  ring

end LowDimensionalTopology.Geometry.Fuchsian
