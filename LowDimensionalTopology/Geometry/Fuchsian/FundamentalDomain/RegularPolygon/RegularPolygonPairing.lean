/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Tangential.PolygonTangentialPolygons
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DiscCircleDistance
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.FiniteCanonicalPolygonPoincare
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TwoMirrorRotations
public import Mathlib.Data.Nat.ModEq

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set InnerProductGeometry
open scoped Complex.UnitDisc Topology UpperHalfPlane ComplexConjugate Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual corner angle in the regular accidental-cycle construction. -/
def regularCycleAngle (n:ℕ) : ℝ:=2*Real.pi/n

theorem regularCycleAngle_mem {n:ℕ} (hn:4<n) :
    regularCycleAngle n∈Ioo (0:ℝ) Real.pi := by
  have hnr:(4:ℝ)<n:=by exact_mod_cast hn
  constructor
  · dsimp only [regularCycleAngle]
    positivity
  · dsimp only [regularCycleAngle]
    apply (div_lt_iff₀ (by linarith only [hnr]:(0:ℝ)<n)).mpr
    nlinarith only [Real.pi_pos,hnr]

theorem regularCycleAngle_sum {n:ℕ} (hn:4<n) :
    ∑ _i:Fin n,regularCycleAngle n<((n:ℝ)-2)*Real.pi := by
  have hnr:(4:ℝ)<n:=by exact_mod_cast hn
  have hn0:(n:ℝ)≠0:=by linarith only [hnr]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,regularCycleAngle]
  have he:(n:ℝ)*(2*Real.pi/n)=2*Real.pi:=by field_simp
  rw [he]
  nlinarith only [Real.pi_pos,hnr]

theorem regularCycleRadius_exists {n:ℕ} (hn:4<n) :
    ∃d:ℝ,0<d ∧ _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun _i:Fin n=>regularCycleAngle
      n) d=Real.pi :=
  _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance_exists_positive _ (fun _=>⟨(regularCycleAngle_mem
    hn).1.le,(regularCycleAngle_mem hn).2⟩)
    (regularCycleAngle_sum hn)

/-- The genuine inscribed radius selected by the proved full-turn angle balance. -/
def regularCycleRadius (n:ℕ) (hn:4<n) : ℝ:=(regularCycleRadius_exists hn).choose

theorem regularCycleRadius_pos {n:ℕ} (hn:4<n) :0<regularCycleRadius n hn:=
  (regularCycleRadius_exists hn).choose_spec.1

theorem regularCycleRadius_balance {n:ℕ} (hn:4<n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (fun _i:Fin n=>regularCycleAngle
      n) (regularCycleRadius n hn)=Real.pi:=
  (regularCycleRadius_exists hn).choose_spec.2

/-- The genuine convex Jordan polygon with these ordered regular native vertices. -/
def regularCyclePolygon (n:ℕ) (hn:4<n) : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n:=
  _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (fun _i:Fin n=>regularCycleAngle
    n) (regularCycleRadius n hn)
    (fun _=>⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩)
    (regularCycleRadius_pos hn) (regularCycleRadius_balance hn)

theorem regularCyclePolygon_isConvex {n:ℕ} (hn:4<n) :
    (regularCyclePolygon n hn).IsConvex:=
  _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_isConvex _ _ _ _ _

theorem regularCyclePolygon_angle {n:ℕ} (hn:4<n) (i:Fin n) :
    (regularCyclePolygon n hn).angle i=regularCycleAngle n:=
  _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle _ _ _ _ _ i

theorem regularCyclePolygon_origin_mem {n:ℕ} (hn:4<n) :
    (0:𝔻)∈(regularCyclePolygon n hn).interior:=
  _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_origin_mem _ _ _ _ _

theorem regularCyclePolygon_vertices_finite {n:ℕ} (hn:4<n) (i:Fin n) :
    ‖((regularCyclePolygon n hn).vertices i:ℂ)‖<1 := by
  have hne:‖((regularCyclePolygon n hn).vertices i:ℂ)‖≠1:=by
    intro he
    change ‖(_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex (fun _i:Fin
      n=>regularCycleAngle n)
      (regularCycleRadius n hn) (fun _=>⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩)
      (regularCycleRadius_pos hn) i:ℂ)‖=1 at he
    have hz:regularCycleAngle n=0:=(_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_ideal_iff _ _ _ _ i).mp he
    exact (regularCycleAngle_mem hn).1.ne' hz
  exact lt_of_le_of_ne ((regularCyclePolygon n hn).vertices i).norm_le_one hne

theorem regularCyclePolygon_half_gap {n:ℕ} (hn:4<n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (regularCycleAngle n) (regularCycleRadius n hn)=Real.pi/n := by
  have hb:=regularCycleRadius_balance hn
  change ∑ _i:Fin n,_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (regularCycleAngle
    n) (regularCycleRadius n hn)=Real.pi at hb
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  apply (eq_div_iff (show (n:ℝ)≠0 by exact_mod_cast (show n≠0 by omega))).mpr
  linarith only [hb]

theorem regularCyclePolygon_inradius_cosh {n:ℕ} (hn:4<n) :
    Real.cosh (regularCycleRadius n hn)=Real.cos (Real.pi/n)/Real.sin (Real.pi/n) := by
  have hnr:(4:ℝ)<n:=by exact_mod_cast hn
  have hs:0<Real.sin (Real.pi/n):=Real.sin_pos_of_pos_of_lt_pi
    (by positivity) ((div_lt_iff₀ (by linarith only [hnr]:(0:ℝ)<n)).mpr (by nlinarith only [Real.pi_pos,hnr]))
  have he:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_sin
    (d:=regularCycleRadius n hn) ⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩
  rw [regularCyclePolygon_half_gap hn,show regularCycleAngle n/2=Real.pi/n by dsimp [regularCycleAngle];ring] at he
  apply (eq_div_iff hs.ne').mpr
  simpa only [mul_comm] using (eq_div_iff (Real.cosh_pos _).ne').mp he

theorem regularCyclePolygon_normalAngle {n:ℕ} (hn:4<n) (k:ℕ) (hk:k≤n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonNormalAngle (fun _i:Fin n=>regularCycleAngle
      n) (regularCycleRadius n hn) k=
      2*k*Real.pi/n := by
  let a:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (regularCycleAngle
    n) (regularCycleRadius n hn)
  have he:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngularPrefix (fun _i:Fin n=>a) k=(k:ℝ)*a:=by
    unfold _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngularPrefix
    have hs:∑ j∈Finset.range k,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngularIncrement (fun _i:Fin n=>a) j=∑ _j∈Finset.range k,a:=by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn:j<n:=lt_of_lt_of_le (Finset.mem_range.mp hj) hk
      simp only [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngularIncrement,dite_eq_left hjn]
    rw [hs]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  change 2*_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngularPrefix (fun _i:Fin n=>a) k=_
  rw [he]
  dsimp only [a]
  rw [regularCyclePolygon_half_gap hn]
  ring

theorem regularCyclePolygon_cornerAngle {n:ℕ} (hn:4<n) (i:Fin n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle (fun _i:Fin n=>regularCycleAngle
      n) (regularCycleRadius n hn) i=
      (2*(i:ℝ)+1)*Real.pi/n := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonCornerNormalAngle,regularCyclePolygon_normalAngle hn i
    i.isLt.le,
    regularCyclePolygon_half_gap hn]
  ring

theorem regularCyclePolygon_klein_vertex {n:ℕ} (hn:4<n) (i:Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate ((regularCyclePolygon n hn).vertices i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (regularCycleAngle
        n) (regularCycleRadius n hn) •
        _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/n) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex
    (fun _i:Fin n=>regularCycleAngle n) (regularCycleRadius n hn)
      (fun _=>⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩)
      (regularCycleRadius_pos hn) i)=_
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate,regularCyclePolygon_cornerAngle hn]

/-- The same actual finite polygon vertex as a point in the open disc. -/
def regularCycleVertex (n:ℕ) (hn:4<n) (i:Fin n) :𝔻:=
  Complex.UnitDisc.mk ((regularCyclePolygon n hn).vertices i:ℂ) (regularCyclePolygon_vertices_finite hn i)

theorem regularCycleVertex_klein_norm {n:ℕ} (hn:4<n) (i:Fin n) :
    ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (regularCycleVertex n hn i)‖=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (regularCycleAngle n) (regularCycleRadius n hn) := by
  have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (regularCycleVertex n hn
    i)=(regularCyclePolygon n hn).vertices i:=Subtype.ext rfl
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,he,regularCyclePolygon_klein_vertex hn,
    norm_smul,Real.norm_eq_abs,abs_of_pos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_pos
      ⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩ (regularCycleRadius_pos hn)),
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm,mul_one]

/-- Every actual regular vertex has the exact source circumradius, for the true
disc density path distance. No radial-distance identity is supplied as a premise. -/
theorem regularCyclePolygon_circumradius {n:ℕ} (hn:4<n) (i:Fin n) :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (regularCycleVertex n hn i))=
      (Real.cos (Real.pi/n)/Real.sin (Real.pi/n))^2 := by
  let d:=regularCycleRadius n hn
  let r:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (regularCycleVertex n hn i)
  let q:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (regularCycleAngle n) d
  let a:=Real.pi/n
  have hnr:(4:ℝ)<n:=by exact_mod_cast hn
  have ha:0<a ∧ a<Real.pi/2:=by
    constructor
    · dsimp only [a];positivity
    · dsimp only [a]
      apply (div_lt_iff₀ (by linarith only [hnr]:(0:ℝ)<n)).mpr
      nlinarith only [Real.pi_pos,hnr]
  have hs:0<Real.sin a:=Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith only [ha.2,Real.pi_pos])
  have hc:0<Real.cos a:=Real.cos_pos_of_mem_Ioo ⟨by linarith only [ha.1,Real.pi_pos],ha.2⟩
  have hq:Real.tanh r=q:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.kleinCoordinate_norm_eq_tanh_distance (regularCycleVertex n hn
      i)).symm.trans
      (regularCycleVertex_klein_norm hn i)
  have hrad:(1-q^2)*Real.cosh r^2=1:=by
    rw [←hq,Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
    nlinarith only [Real.cosh_sq_sub_sinh_sq r]
  have hdef:(1-q^2)*(Real.cosh d*Real.cos a)^2=Real.sin a^2:=by
    have hh:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_defect
      ⟨(regularCycleAngle_mem hn).1.le,(regularCycleAngle_mem hn).2⟩ (regularCycleRadius_pos hn)
    rw [regularCyclePolygon_half_gap hn,
      show regularCycleAngle n/2=a by dsimp only [regularCycleAngle,a];ring] at hh
    exact hh
  have heq:(Real.cosh d*Real.cos a)^2=(Real.sin a*Real.cosh r)^2:=by
    calc
      (Real.cosh d*Real.cos a)^2=
          ((1-q^2)*Real.cosh r^2)*(Real.cosh d*Real.cos a)^2:=by rw [hrad,one_mul]
      _=((1-q^2)*(Real.cosh d*Real.cos a)^2)*Real.cosh r^2:=by ring
      _=Real.sin a^2*Real.cosh r^2:=by rw [hdef]
      _=(Real.sin a*Real.cosh r)^2:=by ring
  have he:Real.cosh d*Real.cos a=Real.sin a*Real.cosh r:=
    (sq_eq_sq₀ (mul_pos (Real.cosh_pos d) hc).le (mul_pos hs (Real.cosh_pos r)).le).mp heq
  have hd:Real.cosh d=Real.cos a/Real.sin a:=regularCyclePolygon_inradius_cosh hn
  rw [hd] at he
  have hh:Real.cos a^2=Real.sin a^2*Real.cosh r:=by
    have hmul:=congrArg (fun x:ℝ=>x*Real.sin a) he
    field_simp [hs.ne'] at hmul
    nlinarith only [hmul]
  change Real.cosh r=(Real.cos a/Real.sin a)^2
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hs.ne')).mpr
  simpa only [mul_comm] using hh.symm


/-- The literal index of the opposite side of a regular 4k-gon. -/
def regularOppositeIndex (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) : Fin (4*k) :=
  ⟨(i.val+2*k)%(4*k),Nat.mod_lt _ (by omega)⟩

theorem regularOppositeIndex_involutive (k : ℕ) (hk : 2≤k) :
    Function.Involutive (regularOppositeIndex k hk) := by
  intro i
  apply Fin.ext
  change ((i.val+2*k)%(4*k)+2*k)%(4*k)=i.val
  rw [Nat.mod_add_mod,show i.val+2*k+2*k=i.val+4*k by omega,Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

theorem regularOppositeIndex_ne (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularOppositeIndex k hk i≠i := by
  intro he
  have hm:=congrArg Fin.val he
  change (i.val+2*k)%(4*k)=i.val at hm
  have hi:=i.isLt
  have hp : 0<2*k:=by omega
  have hh : 2*k<4*k:=by omega
  have hmod : Nat.ModEq (4*k) (i.val+2*k) i.val:=by
    change (i.val+2*k)%(4*k)=i.val%(4*k)
    rwa [Nat.mod_eq_of_lt hi]
  have hd : 4*k∣2*k:=Nat.add_modEq_left_iff.mp hmod
  exact (Nat.le_of_dvd hp hd).not_gt hh

/-- The genuine one-cycle step forced by reversing endpoints across an opposite pair. -/
def regularCanonicalIndex (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) : Fin (4*k) :=
  ⟨(i.val+(2*k+1))%(4*k),Nat.mod_lt _ (by omega)⟩

theorem regularCanonicalMultiplier_square (k : ℕ) :
    (2*k+1)*(2*k+1)=4*k*(k+1)+1 := by ring

/-- Multiplication by the actual canonical step enumerates every original vertex exactly once. -/
def regularCanonicalEnumeration (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) : Fin (4*k) :=
  ⟨(i.val*(2*k+1))%(4*k),Nat.mod_lt _ (by omega)⟩

theorem regularCanonicalEnumeration_involutive (k : ℕ) (hk : 2≤k) :
    Function.Involutive (regularCanonicalEnumeration k hk) := by
  intro i
  apply Fin.ext
  change (((i.val*(2*k+1))%(4*k))*(2*k+1))%(4*k)=i.val
  calc
    _=(i.val*((2*k+1)*(2*k+1)))%(4*k):=by
      rw [Nat.mod_mul_mod,Nat.mul_assoc]
    _=(i.val*(4*k*(k+1)+1))%(4*k):=by rw [regularCanonicalMultiplier_square k]
    _=i.val:=by
      rw [Nat.mul_add,Nat.mul_one,show i.val*(4*k*(k+1))=(i.val*(k+1))*(4*k) by ring]
      simp only [Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_mod]
      exact Nat.mod_eq_of_lt i.isLt

/-- The original 4k vertex labels are one actual complete canonical cyclic orbit. -/
theorem regularCanonicalIndex_iterate (k : ℕ) (hk : 2≤k) (j : ℕ) :
    ((regularCanonicalIndex k hk)^[j]) ⟨0,by omega⟩=
      ⟨(j*(2*k+1))%(4*k),Nat.mod_lt _ (by omega)⟩ := by
  induction j with
  | zero => apply Fin.ext;simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    apply Fin.ext
    change ((j*(2*k+1))%(4*k)+(2*k+1))%(4*k)=((j+1)*(2*k+1))%(4*k)
    rw [Nat.mod_add_mod,Nat.add_mul,Nat.one_mul]

/-- No vertex is omitted from the single canonical index cycle. -/
theorem regularCanonicalIndex_single_cycle (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    ∃j : Fin (4*k),((regularCanonicalIndex k hk)^[j.val]) ⟨0,by omega⟩=i := by
  refine ⟨regularCanonicalEnumeration k hk i,?_⟩
  rw [regularCanonicalIndex_iterate]
  exact regularCanonicalEnumeration_involutive k hk i

/-- Klein coordinates commute with the actual orthogonal maps of the original disc. -/
theorem regular_klein_orthogonal (L : ℂ≃ₗᵢ[ℝ]ℂ) (z : 𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap L z)=L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (L
    (z:ℂ))=L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula (z:ℂ))
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,L.norm_map]
  simpa only [Complex.real_smul] using (L.map_smul (2/(1+‖(z:ℂ)‖^2)) (z:ℂ)).symm

theorem regular_polygonAngleUnit_add (s t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (s+t)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit s*_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit t := by
  simp only [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul]
  rw [Complex.ofReal_add,add_mul,Complex.exp_add]

theorem regular_polygonAngleUnit_periodic (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (t+2*Real.pi)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit t := periodic_circleMap 0 1 t

theorem regularCycleVertex_klein {n : ℕ} (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (regularCycleVertex n hn i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (regularCycleAngle
        n) (regularCycleRadius n hn) •
        _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/n) := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (regularCycleVertex n hn
    i)=(regularCyclePolygon n hn).vertices i:=Subtype.ext rfl
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,he,regularCyclePolygon_klein_vertex hn]

theorem regularCycleVertex_rotation_angle {n : ℕ} (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*Real.pi/n)*_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/n)=
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*((finRotate n i):ℝ)+1)*Real.pi/n) := by
  rw [←regular_polygonAngleUnit_add]
  by_cases hi : i.val+1<n
  · rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygon_finRotate_val_of_succ_lt i hi]
    congr 1
    push_cast
    ring
  · have hil : i.val+1=n:=by omega
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygon_finRotate_val_of_last i hil]
    have hnr : (n:ℝ)≠0:=by exact_mod_cast (show n≠0 by omega)
    have hie : (i:ℝ)+1=n:=by exact_mod_cast hil
    have he : 2*Real.pi/n+(2*(i:ℝ)+1)*Real.pi/n=(2*(0:ℝ)+1)*Real.pi/n+2*Real.pi:=by
      field_simp
      nlinarith only [hie]
    rw [he,regular_polygonAngleUnit_periodic]
    norm_num

theorem regularCycleVertex_rotation (n : ℕ) (hn : 4<n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) false)
      (regularCycleVertex n hn i)=regularCycleVertex n hn (finRotate n i) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_kleinCoordinate.injective
  rw [regular_klein_orthogonal,regularCycleVertex_klein,regularCycleVertex_klein,
    _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
  simp only [Bool.false_eq_true,ite_false,Complex.real_smul]
  have hu : (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*Real.pi/n):=by
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,Circle.coe_exp,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit,
      circleMap_zero,Complex.ofReal_one,one_mul]
  rw [hu,←mul_assoc,mul_comm (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit _)
    ((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate _ _:ℝ):ℂ),
    mul_assoc,regularCycleVertex_rotation_angle hn i]

/-- The genuine hyperbolic rotation carrying the original regular polygon vertices in order. -/
def regularNativeRotation (n : ℕ) : ℍ≃ᵢℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) false)

theorem regularNativeRotation_vertex (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularNativeRotation n
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn)
        (regularCyclePolygon_vertices_finite hn) i)=
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon n hn) (regularCyclePolygon_vertices_finite hn) (finRotate n i) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) false)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (regularCycleVertex n hn i))))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (regularCycleVertex n hn (finRotate n i))
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,regularCycleVertex_rotation]

theorem regularNativeRotation_side (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularNativeRotation n '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (regularCyclePolygon n
      hn) i=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (regularCyclePolygon n hn) (finRotate n i) := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_eq_closedHSegment _
    (regularCyclePolygon_vertices_finite hn),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_image_closedHSegment,regularNativeRotation_vertex,regularNativeRotation_vertex,
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_eq_closedHSegment _ (regularCyclePolygon_vertices_finite hn)]

theorem regular_polygonAngleUnit_add_pi (t : ℝ) : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (t+Real.pi)=-_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit t := by
  rw [regular_polygonAngleUnit_add]
  have hp : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit Real.pi=(-1:ℂ):=by
    apply Complex.ext <;> simp only [_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im,
      Real.cos_pi,Real.sin_pi,Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,neg_zero]
  rw [hp,mul_neg_one]

theorem regular_polygonAngleUnit_sub_pi (t : ℝ) : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (t-Real.pi)=-_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit t := by
  rw [←regular_polygonAngleUnit_periodic (t-Real.pi),show t-Real.pi+2*Real.pi=t+Real.pi by ring,
    regular_polygonAngleUnit_add_pi]

theorem regularCycleVertex_opposite_angle (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*((regularOppositeIndex k hk
      i):ℝ)+1)*Real.pi/(4*k))=
      -_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/(4*k)) := by
  have hk0 : (k:ℝ)≠0:=by exact_mod_cast (show k≠0 by omega)
  change _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*((i.val+2*k)%(4*k):ℕ)+1)*Real.pi/(4*k))=_
  by_cases hi : i.val<2*k
  · rw [Nat.mod_eq_of_lt (show i.val+2*k<4*k by omega)]
    push_cast
    rw [show (2*((i:ℝ)+2*k)+1)*Real.pi/(4*k)=((2*(i:ℝ)+1)*Real.pi/(4*k))+Real.pi by
      field_simp
      ring]
    exact regular_polygonAngleUnit_add_pi _
  · have hle : 4*k ≤ i.val+2*k:=by omega
    rw [Nat.mod_eq_sub_mod hle,Nat.mod_eq_of_lt (show i.val+2*k-4*k<4*k by omega)]
    have hv : ((i.val+2*k-4*k:ℕ):ℝ)=(i:ℝ)-2*k:=by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [hv,show (2*((i:ℝ)-2*k)+1)*Real.pi/(4*k)=((2*(i:ℝ)+1)*Real.pi/(4*k))-Real.pi by
      field_simp
      ring]
    exact regular_polygonAngleUnit_sub_pi _

/-- The actual antipodal isometry sends every original vertex to the original opposite vertex. -/
theorem regularCycleVertex_antipodal (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (Circle.exp Real.pi) false)
      (regularCycleVertex (4*k) (by omega) i)=
        regularCycleVertex (4*k) (by omega) (regularOppositeIndex k hk i) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_kleinCoordinate.injective
  rw [regular_klein_orthogonal,regularCycleVertex_klein,regularCycleVertex_klein,
    _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  rw [regularCycleVertex_opposite_angle k hk i]
  simp only [Bool.false_eq_true,ite_false,Complex.real_smul]
  have hp : (Circle.exp Real.pi:ℂ)=(-1:ℂ):=by
    rw [Circle.coe_exp,Complex.exp_pi_mul_I]
  rw [hp]
  ring

theorem regular_polygonAngleUnit_conj (t : ℝ) :
    conj (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit t)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (-t) := by
  apply Complex.ext <;> simp only [Complex.conj_re,Complex.conj_im,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_re,
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_im,Real.cos_neg,Real.sin_neg]

/-- The actual reflection across the diameter perpendicular to the chosen outward side normal. -/
def regularSideExchangeLinear (n : ℕ) (i : Fin n) : ℂ≃ₗᵢ[ℝ]ℂ :=
  _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap ((Circle.exp Real.pi)*(Circle.exp
    (2*((i:ℝ)+1)*Real.pi/n))^2) true

theorem regularSideExchangeLinear_square (n : ℕ) (i : Fin n) :
    regularSideExchangeLinear n i*regularSideExchangeLinear n i=1 := by
  rw [regularSideExchangeLinear,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul]
  simp only [ite_true,mul_inv_cancel,Bool.xor_self]
  exact _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_one

theorem regularSideExchangeLinear_phase (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularSideExchangeLinear n i (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit
      ((2*(i:ℝ)+1)*Real.pi/n))=
      -_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*((finRotate n i):ℝ)+1)*Real.pi/n) := by
  let b : ℝ:=2*((i:ℝ)+1)*Real.pi/n
  let a : ℝ:=(2*(i:ℝ)+1)*Real.pi/n
  have he (t : ℝ) : (Circle.exp t:ℂ)=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit t:=by
    simp only [Circle.coe_exp,_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul]
  have hp : (Circle.exp Real.pi:ℂ)=(-1:ℂ):=by rw [Circle.coe_exp,Complex.exp_pi_mul_I]
  change _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap ((Circle.exp Real.pi)*(Circle.exp
    b)^2) true (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit a)=_
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
  simp only [ite_true,Circle.coe_mul,Circle.coe_pow,hp,he,regular_polygonAngleUnit_conj]
  calc
    _= -_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (b+b-a):=by
      rw [sub_eq_add_neg,regular_polygonAngleUnit_add,regular_polygonAngleUnit_add]
      ring
    _= -(_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit (2*Real.pi/n)*_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit a):=by
      rw [←regular_polygonAngleUnit_add]
      congr 2
      dsimp only [a,b]
      ring
    _= _:=by rw [regularCycleVertex_rotation_angle hn i]

/-- The actual perpendicular diameter reflection reverses the original side's endpoints. -/
theorem regularSideExchangeLinear_klein_vertex (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularSideExchangeLinear n i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (regularCycleVertex
      n hn i))=
      -_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (regularCycleVertex n hn (finRotate n i)) := by
  rw [regularCycleVertex_klein,regularCycleVertex_klein,map_smul,regularSideExchangeLinear_phase n hn i,smul_neg]

theorem regular_klein_antipodal (z : 𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (Circle.exp Real.pi) false) z)=
      -_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z := by
  rw [regular_klein_orthogonal,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
  simp only [Bool.false_eq_true,ite_false]
  rw [Circle.coe_exp,Complex.exp_pi_mul_I,neg_one_mul]

theorem regularSideExchangeLinear_next_klein_vertex (n : ℕ) (hn : 4<n) (i : Fin n) :
    regularSideExchangeLinear n i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (regularCycleVertex
      n hn (finRotate n i)))=
      -_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (regularCycleVertex n hn i) := by
  have h:=congrArg (regularSideExchangeLinear n i) (regularSideExchangeLinear_klein_vertex n hn i)
  have hs : regularSideExchangeLinear n i
      (regularSideExchangeLinear n i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
        (regularCycleVertex n hn i)))=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (regularCycleVertex n hn i):=by
    have he:=congrArg (fun L : ℂ≃ₗᵢ[ℝ]ℂ=>L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      (regularCycleVertex n hn i)))
      (regularSideExchangeLinear_square n i)
    exact he
  rw [hs,map_neg] at h
  exact neg_eq_iff_eq_neg.mp h.symm

def regularNativeSideExchange (n : ℕ) (i : Fin n) : ℍ≃ᵢℍ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalIsometry (regularSideExchangeLinear n i)

theorem regularNativeSideExchange_vertex (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularNativeSideExchange (4*k) i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega)) i)=
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))
      (regularOppositeIndex k hk (finRotate (4*k) i)) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (regularSideExchangeLinear (4*k) i)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (regularCycleVertex (4*k) (by omega) i))))=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_kleinCoordinate.injective
  rw [regular_klein_orthogonal,regularSideExchangeLinear_klein_vertex,
    ←regular_klein_antipodal,regularCycleVertex_antipodal k hk]
  rfl

theorem regularNativeSideExchange_next_vertex (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularNativeSideExchange (4*k) i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega)) (finRotate (4*k) i))=
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))
      (regularOppositeIndex k hk i) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap (regularSideExchangeLinear (4*k) i)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (regularCycleVertex (4*k) (by omega) (finRotate (4*k) i)))))=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_kleinCoordinate.injective
  rw [regular_klein_orthogonal,regularSideExchangeLinear_next_klein_vertex,
    ←regular_klein_antipodal,regularCycleVertex_antipodal k hk]
  rfl

theorem regularOppositeIndex_rotate (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularOppositeIndex k hk (finRotate (4*k) i)=finRotate (4*k) (regularOppositeIndex k hk i) := by
  have regularCycleNatNonzero : NeZero (4*k):=⟨by omega⟩
  rw [finRotate_apply,finRotate_apply]
  apply Fin.ext
  simp only [regularOppositeIndex,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1<4*k by omega)]
  rw [Nat.mod_add_mod,Nat.mod_add_mod]
  congr 1
  omega

/-- The literal pairing map is the product of the true side reflection and the true
perpendicular diameter reflection; hence it is a genuine ambient hyperbolic isometry. -/
def regularPolygonPairingElement (n : ℕ) (hn : 4<n) (i : Fin n) : ℍ≃ᵢℍ :=
  regularNativeSideExchange n i*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon n hn) i)

theorem regularPolygonPairingElement_vertex (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularPolygonPairingElement (4*k) (by omega) i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega)) i)=
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))
      (finRotate (4*k) (regularOppositeIndex k hk i)) := by
  change regularNativeSideExchange (4*k) i
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry _ _) = _
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_reflection_fixed _ _ _ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem _ (regularCyclePolygon_vertices_finite (by omega)) i),
    regularNativeSideExchange_vertex,regularOppositeIndex_rotate]

theorem regularPolygonPairingElement_next_vertex (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularPolygonPairingElement (4*k) (by omega) i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega)) (finRotate (4*k) i))=
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))
      (regularOppositeIndex k hk i) := by
  change regularNativeSideExchange (4*k) i
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry _ _) = _
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_reflection_fixed _ _ _ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem _ (regularCyclePolygon_vertices_finite (by omega)) i),
    regularNativeSideExchange_next_vertex]

/-- The explicit actual map carries the entire original side exactly onto its opposite. -/
theorem regularPolygonPairingElement_side_image (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularPolygonPairingElement (4*k) (by omega) i '' _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (regularCyclePolygon (4*k) (by omega)) i=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (regularCyclePolygon (4*k) (by omega)) (regularOppositeIndex k hk i) := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_eq_closedHSegment _ (regularCyclePolygon_vertices_finite (by omega)),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.native_image_closedHSegment,regularPolygonPairingElement_vertex k hk i,
    regularPolygonPairingElement_next_vertex k hk i,
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_eq_closedHSegment _ (regularCyclePolygon_vertices_finite (by omega)),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHSegment_comm]
  exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective _ (regularCyclePolygon_vertices_finite (by omega))).ne
    ((regularCyclePolygon (4*k) (by omega)).next_ne_self (regularOppositeIndex k hk i))

theorem regularSideExchangeLinear_opposite (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularSideExchangeLinear (4*k) (regularOppositeIndex k hk i)=regularSideExchangeLinear (4*k) i := by
  have h:=regularSideExchangeLinear_phase (4*k) (by omega) (regularOppositeIndex k hk i)
  rw [←regularOppositeIndex_rotate k hk i] at h
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h
  rw [regularCycleVertex_opposite_angle k hk i,regularCycleVertex_opposite_angle k hk (finRotate (4*k) i),
    map_neg,neg_neg] at h
  have hpoint : regularSideExchangeLinear (4*k) (regularOppositeIndex k hk i)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/(4*k)))=
    regularSideExchangeLinear (4*k) i (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/(4*k))):=by
    have hp:=regularSideExchangeLinear_phase (4*k) (by omega) i
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hp
    rw [hp]
    exact neg_eq_iff_eq_neg.mp h
  have hz : conj (_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit ((2*(i:ℝ)+1)*Real.pi/(4*k)))≠0:=by
    rw [map_ne_zero]
    intro he
    have hn:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm ((2*(i:ℝ)+1)*Real.pi/(4*k))
    rw [he,norm_zero] at hn
    norm_num at hn
  apply LinearIsometryEquiv.ext
  intro z
  simp only [regularSideExchangeLinear,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply,ite_true] at hpoint ⊢
  rw [mul_right_cancel₀ hz hpoint]

theorem regularNativeSideExchange_opposite (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularNativeSideExchange (4*k) (regularOppositeIndex k hk i)=regularNativeSideExchange (4*k) i := by
  unfold regularNativeSideExchange
  rw [regularSideExchangeLinear_opposite k hk i]

theorem regularNativeSideExchange_square (n : ℕ) (i : Fin n) :
    regularNativeSideExchange n i*regularNativeSideExchange n i=1 := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (regularSideExchangeLinear n i)*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertexOrthogonalHom (regularSideExchangeLinear n i)=_
  rw [←map_mul,regularSideExchangeLinear_square,map_one]

/-- An actual native isometry transports a reflection to the genuine reflection in its image line. -/
theorem regular_native_reflection_conjugation (f : ℍ≃ᵢℍ) (L M :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hLine : f '' L.carrier=M.carrier) :
    f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L*f⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry M := by
  obtain ⟨g,hg⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_realGL f.isometry
  obtain ⟨N,hN,href⟩:=L.reflection_conjugation_exists g
  have hNM : N=M:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective (hN.trans (by simpa only [←hg] using hLine))
  rw [hNM] at href
  apply IsometryEquiv.ext
  intro z
  have hinv : f⁻¹ z=g⁻¹ • z := by
    apply f.injective
    rw [f.apply_inv_self,hg]
    exact (smul_inv_smul g z).symm
  change f (L.reflection (f⁻¹ z))=M.reflection z
  rw [hinv,hg]
  exact href z

theorem regularNativeSideExchange_line (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularNativeSideExchange (4*k) i '' (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon (4*k) (by omega)) i).carrier=
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon (4*k) (by omega)) (regularOppositeIndex k hk i)).carrier := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let f:=regularNativeSideExchange (4*k) i
  obtain ⟨g,hg⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isometry_exists_realGL f.isometry
  rw [hg]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_image_line_of_corresponding_points g _ _
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf).ne (Q.next_ne_self i).symm)
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q hf i))
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem Q hf i))
  · rw [←congrFun hg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)]
    change regularNativeSideExchange (4*k) i _∈_
    rw [regularNativeSideExchange_vertex k hk i,regularOppositeIndex_rotate]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q _ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem Q hf _)
  · rw [←congrFun hg (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (finRotate (4*k) i))]
    change regularNativeSideExchange (4*k) i _∈_
    rw [regularNativeSideExchange_next_vertex k hk i]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q _ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q hf _)

theorem regularPolygonPairingElement_inverse (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularPolygonPairingElement (4*k) (by omega) (regularOppositeIndex k hk i)=
      (regularPolygonPairingElement (4*k) (by omega) i)⁻¹ := by
  let f:=regularNativeSideExchange (4*k) i
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (regularCyclePolygon (4*k) (by omega)) i)
  have hc:=regular_native_reflection_conjugation f _ _ (regularNativeSideExchange_line k hk i)
  have hf : f*f=1:=regularNativeSideExchange_square (4*k) i
  have hfi : f⁻¹=f:=inv_eq_of_mul_eq_one_right hf
  have hai : a⁻¹=a:=by
    apply inv_eq_of_mul_eq_one_right
    exact congrArg (fun h : ℍ≃ᵢℍ=>h) (_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneLineReflectionIsometry_sq
      _)
  change regularNativeSideExchange (4*k) (regularOppositeIndex k hk i)*_= (f*a)⁻¹
  rw [regularNativeSideExchange_opposite k hk i,←hc,mul_inv_rev,hfi,hai]
  change f*(f*a*f)=a*f
  rw [mul_assoc f a f,←mul_assoc f f (a*f),hf,one_mul]

/-- The literal opposite-side involution on the original Poincare side type. -/
def regularPolygonSideOpposite (k : ℕ) (hk : 2≤k) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).Side≃
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).Side :=
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))
  (e.symm.trans (Function.Involutive.toPerm (regularOppositeIndex k hk) (regularOppositeIndex_involutive k hk))).trans e

theorem regularPolygonSideOpposite_apply_index (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularPolygonSideOpposite k hk ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))) i)=
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))) (regularOppositeIndex k hk i) := by
  change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv _ _) (regularOppositeIndex k hk
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv _ _).symm
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv _ _) i)))=_
  rw [Equiv.symm_apply_apply]

/-- Genuine side-pairing data for the original finite regular 4k-gon. No cycle or
fundamental-domain condition is included as an input field. -/
def regularPolygonSidePairing (k : ℕ) (hk : 2≤k) :
    _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))) where
  paired:=regularPolygonSideOpposite k hk
  involutive:=by
    intro s
    let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))
    apply e.symm.injective
    change e.symm (e (regularOppositeIndex k hk (e.symm (e (regularOppositeIndex k hk (e.symm s))))))=e.symm s
    simp only [e.symm_apply_apply]
    exact regularOppositeIndex_involutive k hk (e.symm s)
  element s:=regularPolygonPairingElement (4*k) (by omega)
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv _ (regularCyclePolygon_vertices_finite (by omega))).symm s)
  element_paired:=by
    intro s
    let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))
    change regularPolygonPairingElement (4*k) (by omega)
      (e.symm (e (regularOppositeIndex k hk (e.symm s))))=_
    rw [e.symm_apply_apply]
    exact regularPolygonPairingElement_inverse k hk _
  side_image:=by
    intro s
    obtain ⟨i,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega))
      (regularCyclePolygon_vertices_finite (by omega))).surjective s
    change regularPolygonPairingElement (4*k) (by omega)
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv _ (regularCyclePolygon_vertices_finite (by omega))).symm
        ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv _ (regularCyclePolygon_vertices_finite (by omega))) i)) •
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (regularCyclePolygon (4*k) (by omega)) i=_
    rw [Equiv.symm_apply_apply,regularPolygonSideOpposite_apply_index]
    change regularPolygonPairingElement (4*k) (by omega) i ''
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (regularCyclePolygon (4*k) (by omega)) i=_
    exact regularPolygonPairingElement_side_image k hk i

theorem regularCanonicalIndex_eq_rotate_opposite (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    regularCanonicalIndex k hk i=finRotate (4*k) (regularOppositeIndex k hk i) := by
  have regularCanonicalNatNonzero : NeZero (4*k):=⟨by omega⟩
  rw [finRotate_apply]
  apply Fin.ext
  simp only [regularCanonicalIndex,regularOppositeIndex,Fin.val_add,Fin.val_one',
    Nat.mod_eq_of_lt (show 1<4*k by omega)]
  rw [Nat.mod_add_mod]
  congr 1

theorem regularPolygonSidePairing_element_index (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    (regularPolygonSidePairing k hk).element
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))) i)=
      regularPolygonPairingElement (4*k) (by omega) i := by
  change regularPolygonPairingElement (4*k) (by omega)
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv _ _).symm
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv _ _) i))=_
  rw [Equiv.symm_apply_apply]

theorem regularPolygonSidePairing_paired_index (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    (regularPolygonSidePairing k hk).paired
      ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega))) i)=
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv (regularCyclePolygon (4*k) (by omega)) (regularCyclePolygon_vertices_finite (by omega)))
      (regularOppositeIndex k hk i) := regularPolygonSideOpposite_apply_index k hk i

/-- The actual original canonical side-crossing step has the proved single-cycle vertex index. -/
theorem regularPolygonCanonicalStep (k : ℕ) (hk : 2≤k) (i : Fin (4*k))
    (g : (regularPolygonSidePairing k hk).Generated) :
    let Q:=regularCyclePolygon (4*k) (by omega)
    let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
    let S:=regularPolygonSidePairing k hk
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S (g,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
      (g*(S.generator ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf) i))⁻¹,
        _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf (regularCanonicalIndex k hk i)) := by
  let Q:=regularCyclePolygon (4*k) (by omega)
  let hf:=regularCyclePolygon_vertices_finite (show 4<4*k by omega)
  let S:=regularPolygonSidePairing k hk
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
  let hV:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPairing_preserves_vertices Q hf S
  let a:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i
  let c:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap Q hf S hV a
  let j:=regularCanonicalIndex k hk i
  have hmap : S.element (e i) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf j := by
    rw [regularPolygonSidePairing_element_index k hk i,regularPolygonPairingElement_vertex k hk i,
      ←regularCanonicalIndex_eq_rotate_opposite k hk i]
  have hci : c.val.1=j := by
    apply _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap_vertex Q hf S hV a).trans hmap
  have hcs : c.val.2=e (regularOppositeIndex k hk i) := by
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap_side Q hf S hV
      a).trans (regularPolygonSidePairing_paired_index k hk i)
  have hne : e (regularOppositeIndex k hk i)≠e j := by
    apply e.injective.ne
    exact (Q.next_ne_self (regularOppositeIndex k hk i)).symm.trans_eq
      (regularCanonicalIndex_eq_rotate_opposite k hk i).symm
  change (g*(S.generator a.val.2)⁻¹,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertexOtherFlag Q hf
    c)=_
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Prod.ext
    · exact hci
    · change _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertexOtherSide Q hf c.val.1 c.val.2=e j
      rw [hci,hcs]
      exact ite_eq_right hne

theorem regularCyclePolygon_angle_fourk (k : ℕ) (hk : 2≤k) (i : Fin (4*k)) :
    (regularCyclePolygon (4*k) (by omega)).angle i=Real.pi/(2*k) := by
  rw [regularCyclePolygon_angle]
  unfold regularCycleAngle
  push_cast
  ring

/-- The sum here is of the actual geometric corner angles of the original polygon. -/
theorem regularCyclePolygon_angle_sum_fourk (k : ℕ) (hk : 2≤k) :
    ∑i : Fin (4*k),(regularCyclePolygon (4*k) (by omega)).angle i=2*Real.pi := by
  simp only [regularCyclePolygon_angle_fourk k hk,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  have hk0 : (k:ℝ)≠0:=by exact_mod_cast (show k≠0 by omega)
  push_cast
  field_simp
  norm_num

end LowDimensionalTopology.Geometry.Fuchsian
