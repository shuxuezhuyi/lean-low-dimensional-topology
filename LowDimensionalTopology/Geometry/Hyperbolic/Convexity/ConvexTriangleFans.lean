/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.FiniteAreaIdealBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Complex.UnitDisc Topology ENNReal UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Pairwise disjoint actual triangle interiors have additive angular fractions bounded by the actual containing region at any common finite vertex. -/
theorem triangle_family_angularFraction_sum_le {ι : Type*} [Fintype ι]
    (T : ι→ClosedDiscTriangle) (z : 𝔻) (S : Set 𝔻)
    (hz : ∀i,z∈(T i).finiteCarrier) (hsub : ∀i,(T i).interior⊆S)
    (hd : Pairwise (fun i j=>Disjoint (T i).interior (T j).interior)) :
    ∑i,discSubtendedAngularFraction (T i).finiteCarrier z ≤ discSubtendedAngularFraction (_root_.closure S) z := by
  let F:=discOriginNormalizer z
  let A (i : ι):=discRadialDirections (F '' (T i).finiteCarrier)
  have hEq (i : ι) : F '' (T i).finiteCarrier=_root_.closure (F '' (T i).interior) := by
    rw [(T i).finiteCarrier_eq_closure,F.image_closure]
  have hnull (i j : ι) (hij : i≠j) : polygonDirectionMeasure (A i ∩ A j)=0 := by
    rw [show A i=discRadialDirections (_root_.closure (F '' (T i).interior)) from congrArg discRadialDirections (hEq i),
      show A j=discRadialDirections (_root_.closure (F '' (T j).interior)) from congrArg discRadialDirections (hEq j)]
    apply (finite_discRadialDirections_common_closures
      ((T i).interior_discHConvex.isometry_image (discOriginNormalizer_isometry z))
      (F.isOpenMap _ (T i).interior_isOpen) ((T i).interior_nonempty.image F)
      ((T j).interior_discHConvex.isometry_image (discOriginNormalizer_isometry z))
      (F.isOpenMap _ (T j).interior_isOpen) ((T j).interior_nonempty.image F)
      ((hd hij).image F.injective.injOn (subset_univ _) (subset_univ _)) ?_ ?_).measure_zero _
    · rw [←hEq i]
      exact ⟨z,hz i,discOriginNormalizer_apply_self z⟩
    · rw [←hEq j]
      exact ⟨z,hz j,discOriginNormalizer_apply_self z⟩
  have hmeas (i : ι) : NullMeasurableSet (A i) polygonDirectionMeasure :=
    (measurableSet_discRadialDirections
      ((T i).finiteCarrier_hConvex.isometry_image (discOriginNormalizer_isometry z))
      (F.isClosedMap _ (T i).finiteCarrier_isClosed)
      ⟨z,hz i,discOriginNormalizer_apply_self z⟩).nullMeasurableSet
  have hm:=measure_biUnion_finset₀ (μ:=polygonDirectionMeasure) (s:=Finset.univ)
    (f:=A) (fun i _ j _ hij=>hnull i j hij) (fun i _=>hmeas i)
  simp only [Finset.mem_univ,iUnion_true] at hm
  change (∑i,polygonDirectionMeasure (A i)) ≤ _
  rw [←hm]
  apply measure_mono
  apply iUnion_subset
  intro i
  apply discRadialDirections_mono
  apply image_mono
  rw [(T i).finiteCarrier_eq_closure]
  exact closure_mono (hsub i)

/-- The corresponding bound is in true geometric radians, obtained from angular Haar measure. -/
theorem triangle_family_subtendedAngle_sum_le {ι : Type*} [Fintype ι]
    (T : ι→ClosedDiscTriangle) (z : 𝔻) (S : Set 𝔻)
    (hz : ∀i,z∈(T i).finiteCarrier) (hsub : ∀i,(T i).interior⊆S)
    (hd : Pairwise (fun i j=>Disjoint (T i).interior (T j).interior)) :
    ∑i,discSubtendedAngle (T i).finiteCarrier z ≤ discSubtendedAngle (_root_.closure S) z := by
  have hfin (i : ι) : discSubtendedAngularFraction (T i).finiteCarrier z≠⊤:=measure_ne_top polygonDirectionMeasure _
  have hle : (∑i,(discSubtendedAngularFraction (T i).finiteCarrier z).toReal) ≤
      (discSubtendedAngularFraction (_root_.closure S) z).toReal := by
    rw [←ENNReal.toReal_sum (fun i _=>hfin i)]
    exact ENNReal.toReal_mono (measure_ne_top polygonDirectionMeasure _)
      (triangle_family_angularFraction_sum_le T z S hz hsub hd)
  simp only [discSubtendedAngle,←Finset.mul_sum]
  nlinarith only [hle,Real.pi_pos]

/-- Genuine density area is additive on pairwise disjoint actual triangles and bounded by their containing region. -/
theorem triangle_family_density_area_sum_le {ι : Type*} [Fintype ι]
    (T : ι→ClosedDiscTriangle) (S : Set 𝔻) (hsub : ∀i,(T i).interior⊆S)
    (hd : Pairwise (fun i j=>Disjoint (T i).interior (T j).interior)) :
    (∑i,discHyperbolicArea (T i).interior) ≤ discHyperbolicArea S := by
  have hcoe : Topology.IsOpenEmbedding ((↑):𝔻→ℂ):=
    (Metric.isOpen_ball : IsOpen (Metric.ball (0:ℂ) 1)).isOpenEmbedding_subtypeVal
  have hm : discHyperbolicArea (⋃i,(T i).interior)=∑i,discHyperbolicArea (T i).interior := by
    rw [discHyperbolicArea,image_iUnion,measure_iUnion
      (fun i j hij=>(Set.disjoint_image_iff Complex.UnitDisc.coe_injective).mpr (hd hij))
      (fun i=>(hcoe.isOpenMap _ (T i).interior_isOpen).measurableSet)]
    exact tsum_fintype _
  rw [←hm]
  exact measure_mono (image_mono (iUnion_subset hsub))

/-- The actual triangle defects give a quantitative lower bound for the genuine finite area of every containing region. -/
theorem triangle_family_angleDefect_sum_le {ι : Type*} [Fintype ι]
    (T : ι→ClosedDiscTriangle) (S : Set 𝔻) (harea : discHyperbolicArea S≠⊤)
    (hsub : ∀i,(T i).interior⊆S)
    (hd : Pairwise (fun i j=>Disjoint (T i).interior (T j).interior)) :
    (∑i,(Real.pi-(T i).alpha-(T i).beta-(T i).gamma)) ≤ (discHyperbolicArea S).toReal := by
  have he:=ENNReal.toReal_mono harea (triangle_family_density_area_sum_le T S hsub hd)
  rw [ENNReal.toReal_sum (fun i _=>(T i).area_pos_lt_top.2.ne)] at he
  simpa only [ClosedDiscTriangle.area_toReal_eq_angle_defect] using he

/-- Every actual finite or ideal point of the closed triangle is in the literal extended closure of its half-plane interior. -/
theorem ClosedDiscTriangle.halfPlanePoint_mem_extendedClosure (T : ClosedDiscTriangle)
    (p : ClosedHalfPlaneModel) (hp : closedModelCayleyHomeomorph p∈T.closedCarrier) :
    p.val∈_root_.closure (extendedHalfPlanePoint '' T.halfPlaneInterior) := by
  have hdisc : closedModelCayleyHomeomorph p∈discClosedModelClosure T.interior := by
    rwa [←T.closedCarrier_eq_closedModelClosure]
  have he:=mem_image_of_mem closedDiscToExtended hdisc
  rw [discClosedModelClosure_ambient] at he
  have hh:=mem_image_of_mem extendedCayley.symm he
  rw [extendedCayley.symm.image_closure,image_image] at hh
  simp_rw [extendedCayley_symm_coe_disc] at hh
  rw [←image_image,T.discToHalfPlane_image_interior,closedModelCayley_toExtended,
    extendedCayley.symm_apply_apply] at hh
  exact hh

/-- The actual line through a finite point and infinity is its literal vertical geodesic. -/
theorem finiteFan_line_eq_vertical (L : HalfPlaneLine) (z : ℍ)
    (hz : halfPlaneToClosedModel z∈L.closedCarrier)
    (hi : twoIdealInfiniteEndpoint∈L.closedCarrier) : L=HalfPlaneLine.vertical z.re := by
  obtain ⟨x,rfl⟩:=L.eq_vertical_of_infty_ideal
    ((L.closedCarrier_mem_ideal_iff _ twoIdealInfiniteEndpoint_ideal).mp hi)
  have hx:=((HalfPlaneLine.vertical x).closedCarrier_mem_interior_iff z).mp hz
  change z.re=x at hx
  rw [hx]

/-- A true finite-base ideal-apex triangle is constructed from a strict real-coordinate order. -/
def finiteFanHTriangle (a b : ℍ) (hab : a.re < b.re) : ClosedHTriangle where
  a:=halfPlaneToClosedModel a
  b:=halfPlaneToClosedModel b
  c:=twoIdealInfiniteEndpoint
  noncollinear:=by
    rintro ⟨L,ha,hb,hi⟩
    have hLa:=finiteFan_line_eq_vertical L a ha hi
    have hLb:=finiteFan_line_eq_vertical L b hb hi
    have he : a.re=b.re:=HalfPlaneLine.vertical.inj (hLa.symm.trans hLb)
    exact hab.ne he

theorem finiteFanHTriangle_left_line (a b : ℍ) (hab : a.re < b.re) :
    (finiteFanHTriangle a b hab).toDiscTriangle.sideLineB.toHalfPlane=HalfPlaneLine.vertical a.re := by
  let T:=(finiteFanHTriangle a b hab).toDiscTriangle
  apply finiteFan_line_eq_vertical
  · exact (T.sideLineB.closedCarrier_cayley_mem _).mp T.a_mem_sideLineB
  · exact (T.sideLineB.closedCarrier_cayley_mem _).mp T.c_mem_sideLineB

theorem finiteFanHTriangle_right_line (a b : ℍ) (hab : a.re < b.re) :
    (finiteFanHTriangle a b hab).toDiscTriangle.sideLineA.toHalfPlane=HalfPlaneLine.vertical b.re := by
  let T:=(finiteFanHTriangle a b hab).toDiscTriangle
  apply finiteFan_line_eq_vertical
  · exact (T.sideLineA.closedCarrier_cayley_mem _).mp T.b_mem_sideLineA
  · exact (T.sideLineA.closedCarrier_cayley_mem _).mp T.c_mem_sideLineA

/-- The actual finite-base ideal-apex triangle stays in its literal open real-coordinate strip. -/
theorem finiteFanHTriangle_interior_re_bounds (a b : ℍ) (hab : a.re < b.re) :
    (finiteFanHTriangle a b hab).toDiscTriangle.halfPlaneInterior⊆
      {z : ℍ | a.re < z.re ∧ z.re < b.re} := by
  let T:=(finiteFanHTriangle a b hab).toDiscTriangle
  obtain ⟨z,hz⟩:=T.interior_nonempty
  let m:=discToHalfPlane z
  have hm : m∈T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane z)∈T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have he:=T.halfPlaneInterior_eq_components m hm
  rw [finiteFanHTriangle_left_line,finiteFanHTriangle_right_line] at he
  have hsa : T.halfPlaneInterior⊆openHHalfPlane (.vertical a.re) m := fun _ h=>(he ▸ h).2.1
  have hsb : T.halfPlaneInterior⊆openHHalfPlane (.vertical b.re) m := fun _ h=>(he ▸ h).1
  have hma : m.re≠a.re := connectedComponentIn_subset _ _ (hsa hm)
  have hmb : m.re≠b.re := connectedComponentIn_subset _ _ (hsb hm)
  have ha : ((a:ℂ):OnePoint ℂ)∈_root_.closure (extendedHalfPlanePoint '' T.halfPlaneInterior) :=
    T.halfPlanePoint_mem_extendedClosure _ (subset_closedDiscHConvexHull _
      (by change _=T.a ∨ _=T.b ∨ _=T.c;exact Or.inl rfl))
  have hb : ((b:ℂ):OnePoint ℂ)∈_root_.closure (extendedHalfPlanePoint '' T.halfPlaneInterior) :=
    T.halfPlanePoint_mem_extendedClosure _ (subset_closedDiscHConvexHull _
      (by change _=T.a ∨ _=T.b ∨ _=T.c;exact Or.inr (Or.inl rfl)))
  have hpos:=vertical_components_position_of_closure T.halfPlaneInterior (a:ℂ) (b:ℂ) hab ha hb m hma hmb hsa hsb
  intro u hu
  have huA:=hsa hu
  have huB:=hsb hu
  rw [openHHalfPlane_vertical_gt a.re m hpos.1] at huA
  rw [hReCutLt_eq_openHalfPlane b.re m hpos.2] at huB
  exact ⟨huA,huB⟩

/-- The actual fan joining consecutive real-ordered finite points to the genuine infinity endpoint. -/
def finiteHPointFan {n : ℕ} (v : Fin (n+1)→ℍ) (hv : StrictMono (fun i=>(v i).re))
    (i : Fin n) : ClosedDiscTriangle :=
  (finiteFanHTriangle (v i.castSucc) (v i.succ) (hv ((Fin.castSucc_lt_succ (i:=i))))).toDiscTriangle

/-- Real-coordinate strips prove pairwise disjointness of the constructed true fan, including adjacent triangles. -/
theorem finiteHPointFan_pairwise_disjoint {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) :
    Pairwise (fun i j=>Disjoint (finiteHPointFan v hv i).interior (finiteHPointFan v hv j).interior) := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hzi hzj
  have hzH (k : Fin n) (hz : z∈(finiteHPointFan v hv k).interior) :
      discToHalfPlane z∈(finiteHPointFan v hv k).halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane z)∈(finiteHPointFan v hv k).interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hiB:=finiteFanHTriangle_interior_re_bounds _ _ (hv ((Fin.castSucc_lt_succ (i:=i)))) (hzH i hzi)
  have hjB:=finiteFanHTriangle_interior_re_bounds _ _ (hv ((Fin.castSucc_lt_succ (i:=j)))) (hzH j hzj)
  rcases lt_or_gt_of_ne hij with hlt|hlt
  · have horder : (v i.succ).re ≤ (v j.castSucc).re:=hv.monotone (by change i.val + 1  ≤  j.val;have:=hlt;change i.val  <  j.val at this;omega)
    linarith [hiB.2,hjB.1]
  · have horder : (v j.succ).re ≤ (v i.castSucc).re:=hv.monotone (by change j.val + 1  ≤  i.val;have:=hlt;change j.val  <  i.val at this;omega)
    linarith [hjB.2,hiB.1]

/-- Actual finite and ideal closure membership proves that the entire constructed fan lies in the original open convex region. -/
theorem finiteHPointFan_interior_subset {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty)
    (hmem : ∀i,discToClosedModel (halfPlaneToDisc (v i))∈_root_.closure (discToClosedModel '' S))
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S))
    (i : Fin n) : (finiteHPointFan v hv i).interior⊆S := by
  apply (finiteHPointFan v hv i).interior_subset_of_vertices_mem_closedModelClosure hS ho hn
  · change closedModelCayleyHomeomorph (halfPlaneToClosedModel (v i.castSucc))∈_
    rw [closedModelCayley_on_interior]
    exact hmem _
  · change closedModelCayleyHomeomorph (halfPlaneToClosedModel (v i.succ))∈_
    rw [closedModelCayley_on_interior]
    exact hmem _
  · exact hi

/-- The constructed true fan gives a genuine density-area lower bound expressed in its actual finite corner angles. -/
theorem finiteHPointFan_angleDefect_sum_le {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty) (harea : discHyperbolicArea S≠⊤)
    (hmem : ∀i,discToClosedModel (halfPlaneToDisc (v i))∈_root_.closure (discToClosedModel '' S))
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S)) :
    (∑i,(Real.pi-(finiteHPointFan v hv i).alpha-(finiteHPointFan v hv i).beta)) ≤
      (discHyperbolicArea S).toReal := by
  have he:=triangle_family_angleDefect_sum_le (finiteHPointFan v hv) S harea
    (finiteHPointFan_interior_subset v hv hS ho hn hmem hi) (finiteHPointFan_pairwise_disjoint v hv)
  have hγ (i : Fin n) : (finiteHPointFan v hv i).gamma=0:=
    (finiteHPointFan v hv i).gamma_of_ideal
      (closedModelCayley_ideal_norm _ twoIdealInfiniteEndpoint_ideal)
  simpa only [hγ,sub_zero] using he

/-- The actual closed finite carrier satisfies the weak real-coordinate bounds of its true finite-base triangle. -/
theorem finiteFanHTriangle_finiteCarrier_re_bounds (a b : ℍ) (hab : a.re < b.re)
    (z : 𝔻) (hz : z∈(finiteFanHTriangle a b hab).toDiscTriangle.finiteCarrier) :
    a.re ≤ (discToHalfPlane z).re ∧ (discToHalfPlane z).re ≤ b.re := by
  let T:=(finiteFanHTriangle a b hab).toDiscTriangle
  have hzcl : z∈_root_.closure T.interior:=T.finiteCarrier_eq_closure ▸ hz
  have hm:=mem_closure_image continuous_discToHalfPlane.continuousAt hzcl
  rw [T.discToHalfPlane_image_interior] at hm
  have hsub : T.halfPlaneInterior⊆{u : ℍ | a.re ≤ u.re ∧ u.re ≤ b.re} := by
    intro u hu
    exact ⟨(finiteFanHTriangle_interior_re_bounds a b hab hu).1.le,
      (finiteFanHTriangle_interior_re_bounds a b hab hu).2.le⟩
  have hclosed : IsClosed {u : ℍ | a.re ≤ u.re ∧ u.re ≤ b.re}:=
    (isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
      (isClosed_le UpperHalfPlane.continuous_re continuous_const)
  exact closure_minimal hsub hclosed hm

/-- A selected finite fan vertex can lie in a closed fan triangle only as one of that triangle's actual endpoints. -/
theorem finiteHPointFan_vertex_mem_iff {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) (i : Fin n) (k : Fin (n+1)) :
    halfPlaneToDisc (v k)∈(finiteHPointFan v hv i).finiteCarrier↔k=i.castSucc ∨ k=i.succ := by
  constructor
  · intro hk
    have hb:=finiteFanHTriangle_finiteCarrier_re_bounds _ _ (hv (Fin.castSucc_lt_succ (i:=i))) _ hk
    rw [discToHalfPlane_halfPlaneToDisc] at hb
    have hlo:=hv.le_iff_le.mp hb.1
    have hhi:=hv.le_iff_le.mp hb.2
    have hkN : k.val=i.val ∨ k.val=i.val+1 := by
      change i.val ≤ k.val at hlo
      change k.val ≤ i.val+1 at hhi
      omega
    exact hkN.imp Fin.ext Fin.ext
  · rintro (rfl|rfl)
    · change discToClosedModel (halfPlaneToDisc (v i.castSucc))∈(finiteHPointFan v hv i).closedCarrier
      rw [←closedModelCayley_on_interior]
      apply subset_closedDiscHConvexHull
      change _=(finiteHPointFan v hv i).a ∨ _=(finiteHPointFan v hv i).b ∨ _=(finiteHPointFan v hv i).c
      exact Or.inl rfl
    · change discToClosedModel (halfPlaneToDisc (v i.succ))∈(finiteHPointFan v hv i).closedCarrier
      rw [←closedModelCayley_on_interior]
      apply subset_closedDiscHConvexHull
      change _=(finiteHPointFan v hv i).a ∨ _=(finiteHPointFan v hv i).b ∨ _=(finiteHPointFan v hv i).c
      exact Or.inr (Or.inl rfl)

/-- At every actual incident finite fan vertex, the stored triangle corner is its true angular-Haar angle. -/
theorem finiteHPointFan_angleAtPoint_eq_subtendedAngle {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) (i : Fin n) (k : Fin (n+1))
    (hk : halfPlaneToDisc (v k)∈(finiteHPointFan v hv i).finiteCarrier) :
    (finiteHPointFan v hv i).angleAtPoint (discToClosedModel (halfPlaneToDisc (v k)))=
      discSubtendedAngle (finiteHPointFan v hv i).finiteCarrier (halfPlaneToDisc (v k)) := by
  rcases (finiteHPointFan_vertex_mem_iff v hv i k).mp hk with rfl|rfl
  · have ha : (finiteHPointFan v hv i).cornerVertex 0=discToClosedModel (halfPlaneToDisc (v i.castSucc)):=
      closedModelCayley_on_interior _
    rw [←ha,(finiteHPointFan v hv i).angleAtPoint_cornerVertex]
    exact ((finiteHPointFan v hv i).subtendedAngle_at_corner 0 _ ha).symm
  · have hb : (finiteHPointFan v hv i).cornerVertex 1=discToClosedModel (halfPlaneToDisc (v i.succ)):=
      closedModelCayley_on_interior _
    rw [←hb,(finiteHPointFan v hv i).angleAtPoint_cornerVertex]
    exact ((finiteHPointFan v hv i).subtendedAngle_at_corner 1 _ hb).symm

/-- The true angles of every actual triangle incident to a selected finite fan vertex fit inside the containing region's genuine local angle. -/
theorem finiteHPointFan_vertex_angle_budget {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) (S : Set 𝔻)
    (hsub : ∀i,(finiteHPointFan v hv i).interior⊆S) (k : Fin (n+1)) :
    (∑i,(finiteHPointFan v hv i).angleAtPoint (discToClosedModel (halfPlaneToDisc (v k)))) ≤
      discSubtendedAngle (_root_.closure S) (halfPlaneToDisc (v k)) := by
  classical
  let z:=halfPlaneToDisc (v k)
  let I:={i : Fin n // z∈(finiteHPointFan v hv i).finiteCarrier}
  let s:=Finset.univ.filter (fun i : Fin n=>z∈(finiteHPointFan v hv i).finiteCarrier)
  have hs : (∑i,(finiteHPointFan v hv i).angleAtPoint (discToClosedModel z))=
      ∑i∈s,(finiteHPointFan v hv i).angleAtPoint (discToClosedModel z) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _ hi
    apply ClosedDiscTriangle.angleAtPoint_eq_zero_of_not_mem
    change z∉(finiteHPointFan v hv i).finiteCarrier
    simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  calc
    _=∑i∈s,(finiteHPointFan v hv i).angleAtPoint (discToClosedModel z):=hs
    _=∑i : I,(finiteHPointFan v hv i.val).angleAtPoint (discToClosedModel z):=
      Finset.sum_subtype s (by intro x;simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]) _
    _=∑i : I,discSubtendedAngle (finiteHPointFan v hv i.val).finiteCarrier z := by
      apply Finset.sum_congr rfl
      intro i _
      exact finiteHPointFan_angleAtPoint_eq_subtendedAngle v hv i.val k i.property
    _ ≤ discSubtendedAngle (_root_.closure S) z := by
      apply triangle_family_subtendedAngle_sum_le
        (fun i : I=>finiteHPointFan v hv i.val) z S (fun i=>i.property) (fun i=>hsub i.val)
      intro i j hij
      exact finiteHPointFan_pairwise_disjoint v hv (fun he=>hij (Subtype.ext he))

/-- Summing over the actual selected fan vertices counts precisely the two finite corner angles of each actual triangle. -/
theorem finiteHPointFan_triangle_angle_sum {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) (i : Fin n) :
    (∑k,(finiteHPointFan v hv i).angleAtPoint (discToClosedModel (halfPlaneToDisc (v k))))=
      (finiteHPointFan v hv i).alpha+(finiteHPointFan v hv i).beta := by
  classical
  let T:=finiteHPointFan v hv i
  have hab : i.castSucc≠i.succ:=ne_of_lt (Fin.castSucc_lt_succ (i:=i))
  have hs : (∑k,T.angleAtPoint (discToClosedModel (halfPlaneToDisc (v k))))=
      ∑k∈({i.castSucc,i.succ} : Finset (Fin (n+1))),T.angleAtPoint (discToClosedModel (halfPlaneToDisc (v k))) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    apply ClosedDiscTriangle.angleAtPoint_eq_zero_of_not_mem
    change halfPlaneToDisc (v k)∉T.finiteCarrier
    rw [finiteHPointFan_vertex_mem_iff]
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hk
  rw [hs,Finset.sum_pair hab]
  have ha : T.cornerVertex 0=discToClosedModel (halfPlaneToDisc (v i.castSucc)):=
    closedModelCayley_on_interior _
  have hb : T.cornerVertex 1=discToClosedModel (halfPlaneToDisc (v i.succ)):=
    closedModelCayley_on_interior _
  rw [←ha,←hb,T.angleAtPoint_cornerVertex,T.angleAtPoint_cornerVertex]
  rfl

/-- Every selected finite corner is accounted for against the actual containing region, so the total finite triangle angles obey its genuine local angle budget. -/
theorem finiteHPointFan_total_angle_budget {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) (S : Set 𝔻)
    (hsub : ∀i,(finiteHPointFan v hv i).interior⊆S) :
    (∑i,((finiteHPointFan v hv i).alpha+(finiteHPointFan v hv i).beta)) ≤
      ∑k,discSubtendedAngle (_root_.closure S) (halfPlaneToDisc (v k)) := by
  calc
    _=∑i,∑k,(finiteHPointFan v hv i).angleAtPoint (discToClosedModel (halfPlaneToDisc (v k))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (finiteHPointFan_triangle_angle_sum v hv i).symm
    _=∑k,∑i,(finiteHPointFan v hv i).angleAtPoint (discToClosedModel (halfPlaneToDisc (v k))):=Finset.sum_comm
    _ ≤ _:=Finset.sum_le_sum (fun k _=>finiteHPointFan_vertex_angle_budget v hv S hsub k)

/-- The constructed actual fan controls the number of selected points by genuine density area and the original region's true local angles. -/
theorem finiteHPointFan_area_angle_budget {n : ℕ} (v : Fin (n+1)→ℍ)
    (hv : StrictMono (fun i=>(v i).re)) {S : Set 𝔻} (hS : DiscHConvex S)
    (ho : IsOpen S) (hn : S.Nonempty) (harea : discHyperbolicArea S≠⊤)
    (hmem : ∀i,discToClosedModel (halfPlaneToDisc (v i))∈_root_.closure (discToClosedModel '' S))
    (hi : closedModelCayleyHomeomorph twoIdealInfiniteEndpoint∈_root_.closure (discToClosedModel '' S)) :
    (n:ℝ)*Real.pi ≤ (discHyperbolicArea S).toReal+
      ∑k,discSubtendedAngle (_root_.closure S) (halfPlaneToDisc (v k)) := by
  have hd:=finiteHPointFan_angleDefect_sum_le v hv hS ho hn harea hmem hi
  have ha:=finiteHPointFan_total_angle_budget v hv S
    (finiteHPointFan_interior_subset v hv hS ho hn hmem hi)
  have he : (∑i : Fin n,(Real.pi-(finiteHPointFan v hv i).alpha-(finiteHPointFan v hv i).beta))=
      (n:ℝ)*Real.pi-∑i,((finiteHPointFan v hv i).alpha+(finiteHPointFan v hv i).beta) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Finset.sum_add_distrib]
    ring
  rw [he] at hd
  linarith

end LowDimensionalTopology.Geometry.Hyperbolic
