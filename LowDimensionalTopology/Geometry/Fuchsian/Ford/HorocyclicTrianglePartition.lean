/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.HorocyclicCycleBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.OneIdealTriangleTrigonometry
/-! # Genuine horocyclic triangle partitions

Auxiliary angles are measured between actual geodesic rays at actual
upper-half-plane points. Their acuteness and horizontal projection identity
are proved from equal heights and increasing coordinates. The remaining cycle
angle budget still requires the actual group fundamental-domain geometry.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Fuchsian
open Set InnerProductGeometry LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
open scoped UpperHalfPlane OnePoint BigOperators
noncomputable section

def horocyclicUpwardRay (z : ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.canonical z ∞ (by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary])

theorem horocyclicUpwardRay_endpoint (z : ℍ) : (horocyclicUpwardRay z).idealEndpoint=∞ :=
  (horocyclicUpwardRay z).idealEndpoint_unique
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isHLineRay_hRay z ∞ (by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary]))

def horocyclicForwardAngle (z w : ℍ) (hne : z≠w) : ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (horocyclicUpwardRay
    z) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRayThrough z w hne)

theorem horocyclicForwardAngle_coordinates (z w : ℍ) (hne : z≠w) (hx : z.re<w.re)
    (hy : w.im=z.im) :
    Real.sin (horocyclicForwardAngle z w hne)*(2*z.im*w.im*Real.sinh (dist z w))=
      2*z.im*(w.re-z.re) ∧
    Real.cos (horocyclicForwardAngle z w hne)*(2*z.im*w.im*Real.sinh (dist z w))=
      (w.re-z.re)^2 := by
  obtain ⟨hs,hc⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.upwardRay_angle_coordinates hne (horocyclicUpwardRay
    z) (horocyclicUpwardRay_endpoint z)
  refine ⟨?_,?_⟩
  · simpa only [horocyclicForwardAngle,abs_of_pos (sub_pos.mpr hx)] using hs
  · change Real.cos (horocyclicForwardAngle z w hne)*_= _ at hc
    rw [hy] at hc ⊢
    nlinarith only [hc]

theorem horocyclicForwardAngle_acute (z w : ℍ) (hne : z≠w) (hx : z.re<w.re)
    (hy : w.im=z.im) : horocyclicForwardAngle z w hne∈Ioo (0:ℝ) (Real.pi/2) := by
  let θ:=horocyclicForwardAngle z w hne
  have hL : 0<2*z.im*w.im*Real.sinh (dist z w):=by
    exact mul_pos (mul_pos (mul_pos (by norm_num) z.im_pos) w.im_pos)
      (Real.sinh_pos_iff.mpr (dist_pos.mpr hne))
  obtain ⟨hs,hc⟩:=horocyclicForwardAngle_coordinates z w hne hx hy
  have hspos : 0<Real.sin θ:=(mul_pos_iff_of_pos_right hL).mp (hs.symm ▸
    mul_pos (mul_pos (by norm_num) z.im_pos) (sub_pos.mpr hx))
  have hcpos : 0<Real.cos θ:=(mul_pos_iff_of_pos_right hL).mp (hc.symm ▸
    sq_pos_of_ne_zero (sub_ne_zero.mpr hx.ne'))
  have hθ : θ∈Icc (0:ℝ) Real.pi:=⟨angle_nonneg _ _,angle_le_pi _ _⟩
  constructor
  · apply lt_of_le_of_ne hθ.1
    intro he
    have hzero : θ=0:=he.symm
    rw [hzero,Real.sin_zero] at hspos
    exact (lt_irrefl (0:ℝ)) hspos
  · by_contra hn
    have hge : Real.pi/2≤θ:=le_of_not_gt hn
    have hm:=Real.strictAntiOn_cos.antitoneOn
      (show Real.pi/2∈Icc (0:ℝ) Real.pi from ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩) hθ hge
    rw [Real.cos_pi_div_two] at hm
    exact (not_le_of_gt hcpos) hm

/-- The true horizontal projection identity, derived from the actual tangent angle. -/
theorem horocyclicForwardAngle_cot_projection (z w : ℍ) (hne : z≠w) (hx : z.re<w.re)
    (hy : w.im=z.im) : z.im*Real.cot (horocyclicForwardAngle z w hne)=(w.re-z.re)/2 := by
  let θ:=horocyclicForwardAngle z w hne
  let L:=2*z.im*w.im*Real.sinh (dist z w)
  have hL : 0<L:=by
    exact mul_pos (mul_pos (mul_pos (by norm_num) z.im_pos) w.im_pos)
      (Real.sinh_pos_iff.mpr (dist_pos.mpr hne))
  obtain ⟨hs,hc⟩:=horocyclicForwardAngle_coordinates z w hne hx hy
  have hθ:=horocyclicForwardAngle_acute z w hne hx hy
  have hsne : Real.sin θ≠0:=ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2,Real.pi_pos]))
  rw [Real.cot_eq_cos_div_sin,←mul_div_assoc]
  apply (div_eq_iff hsne).mpr
  apply mul_right_cancel₀ hL.ne'
  change (z.im*Real.cos θ)*L=((w.re-z.re)/2*Real.sin θ)*L
  calc
    (z.im*Real.cos θ)*L=z.im*(Real.cos θ*L):=by ring
    _=z.im*(w.re-z.re)^2:=by rw [hc]
    _=((w.re-z.re)/2)*(Real.sin θ*L):=by rw [hs];ring
    _=((w.re-z.re)/2*Real.sin θ)*L:=by ring

theorem fin_adjacent_differences_sum (n : ℕ) (f : Fin (n+1)→ℝ) :
    ∑ i : Fin n,(f i.succ-f i.castSucc)=f (Fin.last n)-f 0 := by
  rw [Finset.sum_sub_distrib]
  have h1:=Fin.sum_univ_succ f
  have h2:=Fin.sum_univ_castSucc f
  linarith only [h1,h2]

def horocyclicPartitionAngles {n : ℕ} (v : Fin (n+1)→ℍ)
    (hx : ∀ i : Fin n,(v i.castSucc).re<(v i.succ).re) (i : Fin n) : ℝ :=
  horocyclicForwardAngle (v i.castSucc) (v i.succ)
    (fun he=> (hx i).ne (congrArg UpperHalfPlane.re he))

theorem horocyclicPartitionAngles_acute {n : ℕ} (v : Fin (n+1)→ℍ)
    (hx : ∀ i : Fin n,(v i.castSucc).re<(v i.succ).re)
    (hy : ∀ i,(v i).im=(v 0).im) (i : Fin n) :
    horocyclicPartitionAngles v hx i∈Ioo (0:ℝ) (Real.pi/2) :=
  horocyclicForwardAngle_acute _ _ _ (hx i) ((hy i.succ).trans (hy i.castSucc).symm)

theorem horocyclicPartitionAngles_projection {n : ℕ} (v : Fin (n+1)→ℍ)
    (hx : ∀ i : Fin n,(v i.castSucc).re<(v i.succ).re)
    (hy : ∀ i,(v i).im=(v 0).im) (hwidth : (v (Fin.last n)).re=(v 0).re+1) :
    ∑ i : Fin n,(v 0).im*Real.cot (horocyclicPartitionAngles v hx i)=1/2 := by
  have hi : ∀ i : Fin n,(v 0).im*Real.cot (horocyclicPartitionAngles v hx i)=
      ((v i.succ).re-(v i.castSucc).re)/2:=by
    intro i
    rw [←hy i.castSucc]
    exact horocyclicForwardAngle_cot_projection _ _ _ (hx i) ((hy i.succ).trans (hy i.castSucc).symm)
  simp_rw [hi]
  rw [←Finset.sum_div,fin_adjacent_differences_sum n (fun i=>(v i).re),hwidth]
  ring

/-- Only the cycle angle budget remains: the true native auxiliary angles and projection are constructed. -/
theorem horocyclicPartition_height_bound {n q : ℕ} (hn : 0<n) (hq : 0<q) (hqn : 2<q*n)
    (v : Fin (n+1)→ℍ) (hx : ∀ i : Fin n,(v i.castSucc).re<(v i.succ).re)
    (hy : ∀ i,(v i).im=(v 0).im) (hwidth : (v (Fin.last n)).re=(v 0).re+1)
    (hsum : ∑ i : Fin n,horocyclicPartitionAngles v hx i≤Real.pi/(q:ℝ)) :
    ∀ i,(v i).im≤cycleHeightBound q n := by
  have h:=horocyclic_height_bound_from_angle_partition hn hq hqn (horocyclicPartitionAngles v hx) (v 0)
    (horocyclicPartitionAngles_acute v hx hy) hsum (horocyclicPartitionAngles_projection v hx hy hwidth)
  intro i
  rw [hy i]
  exact h

end
end LowDimensionalTopology.Geometry.Fuchsian
