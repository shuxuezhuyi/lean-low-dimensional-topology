module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleSignatures
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Topology
open scoped UpperHalfPlane

theorem closedTriangleFiniteCornerOrderList_perm_corner_list
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma)
    (l:List {i:Fin 3|0<closedTriangleCornerAngle T i}) (hNd:l.Nodup)
    (hAll:∀i,i∈l) :
    (closedTriangleFiniteCornerOrderList T ha hb hc).Perm
      (l.map (closedTriangleFiniteCornerOrder T ha hb hc)) := by
  classical
  let V:={i:Fin 3|0<closedTriangleCornerAngle T i}
  let E:Fin (Fintype.card V)≃V:=(Fintype.equivFin V).symm
  have hP:(List.ofFn (fun j=>E j)).Perm l:=by
    apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr E.injective) hNd).mpr
    intro i
    constructor
    · intro _h;exact hAll i
    · intro _h;exact List.mem_ofFn.mpr ⟨E.symm i,E.apply_symm_apply i⟩
  change (List.ofFn (fun j=>closedTriangleFiniteCornerOrder T ha hb hc (E j))).Perm _
  simpa only [List.map_ofFn,Function.comp_def] using hP.map (closedTriangleFiniteCornerOrder T ha hb hc)

/-- Any complete literal list of actual finite corners computes the original cofinite signature, preserving every repeated order. -/
theorem closedTriangle_actual_signature_of_corner_list
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (l:List {i:Fin 3|0<closedTriangleCornerAngle T i}) (hNd:l.Nodup) (hAll:∀i,i∈l) :
    HasCofiniteFuchsianSignature P.asFuchsianDisc 0
      (l.map (closedTriangleFiniteCornerOrder T ha hb hc))
      (Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}) := by
  have h:=closedTriangle_actual_cofinite_signature T ha hb hc P
  refine ⟨h.ellipticClassesFinite,h.parabolicClassesFinite,h.compact,h.topologicalGenus,?_,h.cuspCount⟩
  exact (closedTriangleFiniteCornerOrderList_perm_corner_list T ha hb hc l hNd hAll).symm.trans h.ellipticOrders

/-- The actual original two-ideal triangle has precisely one elliptic order p and exactly two genuine cusp classes. -/
theorem closedTriangle_actual_signature_two_ideal
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p:ℕ)
    (hp:2≤p)
    (hα:T.alpha=Real.pi/(p:ℝ)) (hβ:T.beta=0) (hγ:T.gamma=0)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [p] 2 := by
  classical
  have ha:IsIntegralTriangleAngle T.alpha:=Or.inr ⟨p,hp,hα⟩
  have hb:IsIntegralTriangleAngle T.beta:=Or.inl hβ
  have hc:IsIntegralTriangleAngle T.gamma:=Or.inl hγ
  have hpos:0<T.alpha:=by rw [hα];exact div_pos Real.pi_pos (by positivity)
  let i0:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨0,hpos⟩
  have hAll:∀i:{i:Fin 3|0<closedTriangleCornerAngle T i},i∈[i0]:=by
    rintro ⟨i,hi⟩
    fin_cases i
    · exact List.mem_singleton.mpr (Subtype.ext rfl)
    · change 0<T.beta at hi
      rw [hβ] at hi
      exact (lt_irrefl _ hi).elim
    · change 0<T.gamma at hi
      rw [hγ] at hi
      exact (lt_irrefl _ hi).elim
  have hList:([i0].map (closedTriangleFiniteCornerOrder T ha hb hc))=[p]:=by
    simp only [List.map_cons,List.map_nil]
    rw [closedTriangleFiniteCornerOrder_eq_of_angle T ha hb hc i0 p hp hα]
  have hCount:Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}=2:=by
    have heq:{i:Fin 3|closedTriangleCornerAngle T i=0}=({1,2}:Set (Fin 3)):=by
      ext i
      fin_cases i
      · change (T.alpha=0)↔((0:Fin 3)=1 ∨(0:Fin 3)=2)
        norm_num [ne_of_gt hpos]
      · change (T.beta=0)↔((1:Fin 3)=1 ∨(1:Fin 3)=2)
        simp only [hβ,true_or]
      · change (T.gamma=0)↔((2:Fin 3)=1 ∨(2:Fin 3)=2)
        simp only [hγ,or_true]
    rw [heq]
    change ({1,2}:Set (Fin 3)).ncard=2
    simp
  have h:=closedTriangle_actual_signature_of_corner_list T ha hb hc P [i0] (by simp) hAll
  simpa only [hList,hCount] using h


/-- The actual original one-ideal triangle has the complete two-entry elliptic order list and exactly one cusp. -/
theorem closedTriangle_actual_signature_one_ideal
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p q:ℕ)
    (hp:2≤p)
    (hq:2≤q)
    (hα:T.alpha=Real.pi/(p:ℝ)) (hβ:T.beta=Real.pi/(q:ℝ)) (hγ:T.gamma=0)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [p,q] 1 := by
  classical
  have ha:IsIntegralTriangleAngle T.alpha:=Or.inr ⟨p,hp,hα⟩
  have hb:IsIntegralTriangleAngle T.beta:=Or.inr ⟨q,hq,hβ⟩
  have hc:IsIntegralTriangleAngle T.gamma:=Or.inl hγ
  have hpos:0<T.alpha:=by rw [hα];exact div_pos Real.pi_pos (by positivity)
  have hposB:0<T.beta:=by rw [hβ];exact div_pos Real.pi_pos (by positivity)
  let i0:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨0,hpos⟩
  let i1:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨1,hposB⟩
  have hAll:∀i:{i:Fin 3|0<closedTriangleCornerAngle T i},i∈[i0,i1]:=by
    rintro ⟨i,hi⟩
    fin_cases i
    · exact List.mem_cons.mpr (Or.inl (Subtype.ext rfl))
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr (Subtype.ext rfl)))
    · change 0<T.gamma at hi
      rw [hγ] at hi
      exact (lt_irrefl _ hi).elim
  have hList:([i0,i1].map (closedTriangleFiniteCornerOrder T ha hb hc))=[p,q]:=by
    simp only [List.map_cons,List.map_nil]
    rw [closedTriangleFiniteCornerOrder_eq_of_angle T ha hb hc i0 p hp hα,
      closedTriangleFiniteCornerOrder_eq_of_angle T ha hb hc i1 q hq hβ]
  have hCount:Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}=1:=by
    have heq:{i:Fin 3|closedTriangleCornerAngle T i=0}=({2}:Set (Fin 3)):=by
      ext i
      fin_cases i
      · change (T.alpha=0)↔((0:Fin 3)=2)
        norm_num [ne_of_gt hpos]
      · change (T.beta=0)↔((1:Fin 3)=2)
        norm_num [ne_of_gt hposB]
      · change (T.gamma=0)↔((2:Fin 3)=2)
        simp only [hγ]
    rw [heq]
    change ({2}:Set (Fin 3)).ncard=1
    simp
  have hNd:[i0,i1].Nodup:=by simp [i0,i1]
  have h:=closedTriangle_actual_signature_of_corner_list T ha hb hc P [i0,i1] hNd hAll
  simpa only [hList,hCount] using h

/-- The actual original three-ideal triangle has no elliptic class and exactly three genuine cusp classes. -/
theorem closedTriangle_actual_signature_three_ideal
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα:T.alpha=0) (hβ:T.beta=0) (hγ:T.gamma=0)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [] 3 := by
  classical
  have ha:IsIntegralTriangleAngle T.alpha:=Or.inl hα
  have hb:IsIntegralTriangleAngle T.beta:=Or.inl hβ
  have hc:IsIntegralTriangleAngle T.gamma:=Or.inl hγ
  have hAngle:∀i:Fin 3,closedTriangleCornerAngle T i=0:=by
    intro i
    fin_cases i <;> assumption
  have hAll:∀i:{i:Fin 3|0<closedTriangleCornerAngle T i},i∈([]:List _) :=by
    intro i
    have hi:=i.property
    change 0<closedTriangleCornerAngle T i.val at hi
    rw [hAngle] at hi
    exact (lt_irrefl _ hi).elim
  have hCount:Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}=3:=by
    have heq:{i:Fin 3|closedTriangleCornerAngle T i=0}=(univ:Set (Fin 3)):=by
      ext i
      exact iff_true_intro (hAngle i)
    rw [heq]
    simp
  have h:=closedTriangle_actual_signature_of_corner_list T ha hb hc P [] (by simp) hAll
  simpa only [List.map_nil,hCount] using h


/-- The actual original all-finite triangle has exactly its three reciprocal-angle orders, including repetitions, and no cusp. -/
theorem closedTriangle_actual_signature_finite
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p q r:ℕ)
    (hp:2≤p) (hq:2≤q) (hr:2≤r)
    (hα:T.alpha=Real.pi/(p:ℝ)) (hβ:T.beta=Real.pi/(q:ℝ)) (hγ:T.gamma=Real.pi/(r:ℝ))
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [p,q,r] 0 := by
  classical
  have ha:IsIntegralTriangleAngle T.alpha:=Or.inr ⟨p,hp,hα⟩
  have hb:IsIntegralTriangleAngle T.beta:=Or.inr ⟨q,hq,hβ⟩
  have hc:IsIntegralTriangleAngle T.gamma:=Or.inr ⟨r,hr,hγ⟩
  have hpos:0<T.alpha:=by rw [hα];exact div_pos Real.pi_pos (by positivity)
  have hposB:0<T.beta:=by rw [hβ];exact div_pos Real.pi_pos (by positivity)
  have hposC:0<T.gamma:=by rw [hγ];exact div_pos Real.pi_pos (by positivity)
  let i0:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨0,hpos⟩
  let i1:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨1,hposB⟩
  let i2:{i:Fin 3|0<closedTriangleCornerAngle T i}:=⟨2,hposC⟩
  have hAll:∀i:{i:Fin 3|0<closedTriangleCornerAngle T i},i∈[i0,i1,i2]:=by
    rintro ⟨i,_hi⟩
    fin_cases i
    · exact List.mem_cons.mpr (Or.inl (Subtype.ext rfl))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl (Subtype.ext rfl))))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_singleton.mpr (Subtype.ext rfl)))))
  have hList:([i0,i1,i2].map (closedTriangleFiniteCornerOrder T ha hb hc))=[p,q,r]:=by
    simp only [List.map_cons,List.map_nil]
    rw [closedTriangleFiniteCornerOrder_eq_of_angle T ha hb hc i0 p hp hα,
      closedTriangleFiniteCornerOrder_eq_of_angle T ha hb hc i1 q hq hβ,
      closedTriangleFiniteCornerOrder_eq_of_angle T ha hb hc i2 r hr hγ]
  have hCount:Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}=0:=by
    have hpositive:∀i:Fin 3,0<closedTriangleCornerAngle T i:=by intro i;fin_cases i <;> assumption
    have heq:{i:Fin 3|closedTriangleCornerAngle T i=0}=(∅:Set (Fin 3)):=by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (ne_of_gt (hpositive i)) hi
    rw [heq]
    change (∅:Set (Fin 3)).ncard=0
    simp
  have hNd:[i0,i1,i2].Nodup:=by simp [i0,i1,i2]
  have h:=closedTriangle_actual_signature_of_corner_list T ha hb hc P [i0,i1,i2] hNd hAll
  simpa only [hList,hCount] using h

end LowDimensionalTopology.Geometry.Fuchsian
