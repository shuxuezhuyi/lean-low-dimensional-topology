/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralSectors
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology InnerProductGeometry
open scoped NNReal
namespace LowDimensionalTopology.Geometry.Euclidean
local notation "𝔸" => AddCircle (2*Real.pi)

/-- A genuine short centred direction arc is exactly the literal exponential interval. -/
theorem circle_short_arc_eq_exp_interval (P : ℝ) (hP0 : 0<P) (hPπ : P<Real.pi) :
    polygonClosedDirectionArc ((P/2:ℝ):𝔸) (P/2)=Circle.exp '' Icc (0:ℝ) P := by
  ext u
  constructor
  · rintro ⟨y,hy,he⟩
    have hyu : y=AddCircle.homeomorphCircle'.symm u:=by
      rw [←he]
      exact (AddCircle.homeomorphCircle'.symm_apply_apply y).symm
    rw [hyu] at hy
    let t:=Complex.arg (u:ℂ)
    have htlo : -Real.pi<t:=Complex.neg_pi_lt_arg _
    have hthi : t≤Real.pi:=Complex.arg_le_pi _
    change dist ((t:ℝ):𝔸) ((P/2:ℝ):𝔸)≤P/2 at hy
    rw [dist_eq_norm,←AddCircle.coe_sub] at hy
    have hd : |t-P/2|≤Real.pi+P/2:=abs_le.mpr ⟨by linarith,by linarith⟩
    rw [angularCircle_norm_coe_min (x:=t-P/2) (by linarith)] at hy
    have ht : t∈Icc (0:ℝ) P:=by
      rcases min_le_iff.mp hy with hh|hh
      · have ha:=abs_le.mp hh
        exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
      · exfalso
        linarith
    exact ⟨t,ht,Circle.exp_arg u⟩
  · rintro ⟨t,ht,rfl⟩
    refine ⟨(t:𝔸),?_,rfl⟩
    change dist ((t:ℝ):𝔸) ((P/2:ℝ):𝔸)≤P/2
    rw [dist_eq_norm,←AddCircle.coe_sub]
    have ha : |t-P/2|≤P/2:=abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [(AddCircle.norm_coe_eq_abs_iff (2*Real.pi) (by positivity : 2*Real.pi≠0)).mpr (by
      rw [abs_of_pos (by positivity : 0<2*Real.pi)]
      linarith)]
    exact ha

/-- The literal short unit arc is precisely the genuine nonnegative span of its two endpoints. -/
theorem finiteRotationClosedArc_span (m : ℕ) (hm : 3≤m) (u : Circle) :
    u∈finiteRotationClosedArc m ↔
      (u:ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (finiteRotationPeriod m):ℂ)} := by
  have hmR : (3:ℝ)≤(m:ℝ):=by exact_mod_cast hm
  have hmpos : 0<m:=by omega
  have hP0:=finiteRotationPeriod_pos m hmpos
  have hPπ : finiteRotationPeriod m<Real.pi:=by
    dsimp only [finiteRotationPeriod]
    apply (div_lt_iff₀ (by positivity : 0<(m:ℝ))).mpr
    nlinarith [Real.pi_pos]
  have hh:=circle_mem_positiveCone_endpoints (finiteRotationPeriod m/2)
    (r:=finiteRotationPeriod m/2) (by positivity) (by linarith) u
  rw [circle_short_arc_eq_exp_interval (finiteRotationPeriod m) hP0 hPπ] at hh
  have he0 : finiteRotationPeriod m/2-finiteRotationPeriod m/2=0:=sub_self _
  have heP : finiteRotationPeriod m/2+finiteRotationPeriod m/2=finiteRotationPeriod m:=by ring
  simpa only [he0,heP,Circle.exp_zero,Circle.coe_one,finiteRotationClosedArc] using hh.symm

/-- The actual closed short planar sector is the ordinary nonnegative cone of its two rays. -/
theorem finiteRotationClosedPlaneSector_eq_span (m : ℕ) (hm : 3≤m) :
    finiteRotationClosedPlaneSector m=
      (Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (finiteRotationPeriod m):ℂ)} : Set ℂ) := by
  let C:=Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (finiteRotationPeriod m):ℂ)}
  ext z
  by_cases hz : z=0
  · subst z
    change (0:ℂ)∈finiteRotationClosedPlaneSector m ↔ (0:ℂ)∈C
    exact iff_of_true (Or.inl rfl) C.zero_mem
  · let w : {z : ℂ // z≠0}:=⟨z,hz⟩
    have hc : z∈finiteRotationClosedPlaneSector m ↔ finiteSectorDirection w∈finiteRotationClosedArc m:=by
      constructor
      · rintro (h0|⟨v,hv,hv_eq⟩)
        · exact False.elim (hz h0)
        · have he : v=w:=Subtype.ext hv_eq
          exact he ▸ hv
      · intro hw
        exact Or.inr ⟨w,hw,rfl⟩
    rw [hc,finiteRotationClosedArc_span m hm]
    let r : ℝ≥0:=⟨‖z‖,(norm_nonneg z)⟩
    have hr : r≠0:=by
      intro he
      have he' : ‖z‖=0:=congrArg (fun x : ℝ≥0=>(x:ℝ)) he
      exact hz (norm_eq_zero.mp he')
    have hrep : r • (finiteSectorDirection w:ℂ)=z:=finiteSectorDirection_reconstruct w
    change (finiteSectorDirection w:ℂ)∈C ↔ z∈C
    rw [←hrep]
    exact (Submodule.smul_mem_iff C hr).symm

end LowDimensionalTopology.Geometry.Euclidean
