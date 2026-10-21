/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.IntersectingHyperbolicProducts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The product of the signed axis parameter and half trace is intrinsic to the actual map. -/
theorem hAxisSignedTrace_congr {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (L : HalfPlaneLine) (he : realSLMobius A=realSLMobius B) :
    (Matrix.trace A.val/2)*hAxisSignedSine A L=(Matrix.trace B.val/2)*hAxisSignedSine B L := by
  rcases (realSLMobius_eq_iff_sign A B).mp he with he | he
  · rw [he]
  · rw [he,hAxisSignedSine_neg,Matrix.SpecialLinearGroup.coe_neg,Matrix.trace_neg]
    ring

/-- The half-turn partner's actual horizontal direction determines the centered matrix sign
at the apex of a genuine concentric geodesic. -/
theorem hHalfTurn_concentric_signed_trace
    (P W : Matrix.SpecialLinearGroup (Fin 2) ℝ) (r : ℝ) (hr : 0<r) (w : ℍ)
    (hP : IsHalfTurnAt P (metricProbe 0 r hr)) (hW : IsHalfTurnAt W w) :
    ((Matrix.trace (W*P).val/2)*hAxisSignedSine (W*P) (.circle 0 r hr))*w.im=
      Real.cosh (dist (metricProbe 0 r hr) w)*w.re := by
  have hpc:=hSL_elliptic_center_coefficients P hP.elliptic
  have hwc:=hSL_elliptic_center_coefficients W hW.elliptic
  rw [hP.center_eq,(realSLMobius_order_two_iff_trace_zero P hP.ne_one).mp hP.1] at hpc
  rw [hW.center_eq,(realSLMobius_order_two_iff_trace_zero W hW.ne_one).mp hW.1] at hwc
  have hp00 : P 0 0=0 := by simpa [metricProbe] using hpc.1
  have hw11 : W 1 1= -W 1 0*w.re := by simpa using hwc.2.1
  have hc : (W*P) 1 0= -W 1 0*P 1 0*w.re := by
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    rw [hp00,hw11]
    ring
  have hpsq : (P 1 0*r)^2=1 := by
    have he:=congrArg (fun x:ℝ=>x^2) hP.center_coefficient_abs
    have hpim : (metricProbe 0 r hr).im=r := by simp [metricProbe]
    rw [hpim,sq_abs,one_pow] at he
    exact he
  have hwsq : (W 1 0*w.im)^2=1 := by
    have he:=congrArg (fun x:ℝ=>x^2) hW.center_coefficient_abs
    simpa only [sq_abs,one_pow] using he
  rw [hHalfTurn_product_trace W P w (metricProbe 0 r hr) hW hP,dist_comm w]
  dsimp only [hAxisSignedSine,hAxisReflectionCoefficient,HalfPlaneLine.reflectionScale]
  rw [hc]
  change (-Real.cosh (dist (metricProbe 0 r hr) w)*(W 1 0*w.im)*(P 1 0*r))*
    ((-W 1 0*P 1 0*w.re)*r)*w.im= _
  calc
    _ = Real.cosh (dist (metricProbe 0 r hr) w)*(W 1 0*w.im)^2*(P 1 0*r)^2*w.re := by ring
    _ = _ := by rw [hpsq,hwsq];ring

/-- At the actual circle apex, the signed matrix coefficient points against the default
circle tangent precisely when the genuine attractive ray points with it. -/
theorem hHyperbolic_concentric_attractive_direction
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1)
    (ht : 4 < (Matrix.trace A.val)^2) (r : ℝ) (hr : 0<r)
    (haxis : hHyperbolicAxis A hA ht=.circle 0 r hr)
    (R : HRayAt (metricProbe 0 r hr))
    (hR : Mobius.MobiusAttractiveFixedPoint (realSLMobius A) R.idealEndpoint) :
    R.supportLine=.circle 0 r hr ∧
      0< -((Matrix.trace A.val/2)*hAxisSignedSine A (.circle 0 r hr))*R.tangentSign := by
  let p:=metricProbe 0 r hr
  have hp : p∈(hHyperbolicAxis A hA ht).carrier := by
    rw [haxis]
    change ‖(p:ℂ)-(0:ℂ)‖=r
    simp [p,metricProbe,Complex.norm_def]
    exact Real.sqrt_mul_self hr.le
  obtain ⟨w,⟨hw,hAw,hT⟩,_⟩:=realSL_hyperbolic_halfturn_factor A hA ht p hp
  have hpw : p≠w := by
    intro he
    rw [←he,dist_self,mul_zero] at hT
    have hh:=hHyperbolic_translationLength_pos A hA ht
    linarith
  let R':=hRayThrough p w hpw
  have hReq : R=R' := HRayAt.idealEndpoint_injective p
    (hHyperbolic_attractive_fixedPoint_unique A ht hR
      (realSL_hyperbolic_halfturn_ray_attractive A hA ht p w hpw hp hAw))
  rw [hReq]
  have hRL : R'.supportLine=.circle 0 r hr := by
    rw [←haxis]
    exact R'.supportLine.eq_of_two_points _ hpw R'.start_mem_support
      (R'.subset_support (hRayThrough_mem p w hpw)) hp hw
  refine ⟨hRL,?_⟩
  have hforward:=R'.longitudinal_forward_pos (hRayThrough_mem p w hpw) hpw.symm
  change 0<R'.tangentSign*(R'.supportLine.longitudinal (w:ℂ)-R'.supportLine.longitudinal (p:ℂ)) at hforward
  rw [hRL] at hforward
  change 0<R'.tangentSign*(-w.re- -p.re) at hforward
  change 0<R'.tangentSign*(-w.re- -(0:ℝ)) at hforward
  obtain ⟨P,W,hP,hW,hproj⟩:=hAw
  have hproj' : realSLMobius A=realSLMobius (W*P) := by rw [map_mul];exact hproj
  have he:=hHalfTurn_concentric_signed_trace P W r hr w hP hW
  rw [←hAxisSignedTrace_congr (.circle 0 r hr) hproj'] at he
  have hsign : ((Matrix.trace A.val/2)*hAxisSignedSine A (.circle 0 r hr))*R'.tangentSign*w.im=
      Real.cosh (dist p w)*(R'.tangentSign*w.re) := by linear_combination R'.tangentSign*he
  have hneg : R'.tangentSign*w.re<0 := by nlinarith [hforward]
  have hneg' := mul_neg_of_pos_of_neg (Real.cosh_pos (dist p w)) hneg
  rw [←hsign] at hneg'
  have hcoef : ((Matrix.trace A.val/2)*hAxisSignedSine A (.circle 0 r hr))*R'.tangentSign<0 := by
    by_contra! hn
    have hh:=mul_nonneg hn w.im_pos.le
    linarith
  nlinarith


/-- The signed Lorentz pairing of concentric axes is positive, with its exact literal value. -/
theorem hAxisPairing_concentric (r s : ℝ) (hr : 0<r) (hs : 0<s) :
    hAxisPairing (.circle 0 r hr) (.circle 0 s hs)=(r^2+s^2)/(2*r*s) := by
  simp only [hAxisPairing,HalfPlaneLine.incenterNormal,HalfPlaneLine.incenterOffset,
    _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,zero_div,mul_zero,add_zero]
  field_simp
  ring

/-- At the two actual apices of concentric axes, the intrinsic relative sign is exactly
the product of the genuine forward-ray tangent signs. -/
theorem hRelativeAxisSign_concentric_attractive
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (r s : ℝ) (hr : 0<r) (hs : 0<s)
    (haxisA : hHyperbolicAxis A hA htA=.circle 0 r hr)
    (haxisB : hHyperbolicAxis B hB htB=.circle 0 s hs)
    (R : HRayAt (metricProbe 0 r hr)) (S : HRayAt (metricProbe 0 s hs))
    (hR : Mobius.MobiusAttractiveFixedPoint (realSLMobius A) R.idealEndpoint)
    (hS : Mobius.MobiusAttractiveFixedPoint (realSLMobius B) S.idealEndpoint) :
    hRelativeAxisSign A B (.circle 0 r hr) (.circle 0 s hs)=R.tangentSign*S.tangentSign := by
  have ha:=(hHyperbolic_concentric_attractive_direction A hA htA r hr haxisA R hR).2
  have hb:=(hHyperbolic_concentric_attractive_direction B hB htB s hs haxisB S hS).2
  have hp : 0<hAxisPairing (.circle 0 r hr) (.circle 0 s hs) := by
    rw [hAxisPairing_concentric r s hr hs]
    exact div_pos (by nlinarith [sq_pos_of_pos hr,sq_pos_of_pos hs]) (by positivity)
  have hRsg : R.tangentSign=1 ∨ R.tangentSign= -1 := by
    classical
    unfold HRayAt.tangentSign
    split_ifs <;> simp
  have hSsg : S.tangentSign=1 ∨ S.tangentSign= -1 := by
    classical
    unfold HRayAt.tangentSign
    split_ifs <;> simp
  unfold hRelativeAxisSign
  rw [show (Matrix.trace A.val/2*(Matrix.trace B.val/2))*
      (hAxisSignedSine A (.circle 0 r hr)*hAxisSignedSine B (.circle 0 s hs)*
        hAxisPairing (.circle 0 r hr) (.circle 0 s hs))=
      ((Matrix.trace A.val/2)*hAxisSignedSine A (.circle 0 r hr))*
      ((Matrix.trace B.val/2)*hAxisSignedSine B (.circle 0 s hs))*
        hAxisPairing (.circle 0 r hr) (.circle 0 s hs) by ring]
  let x:=(Matrix.trace A.val/2)*hAxisSignedSine A (.circle 0 r hr)
  let y:=(Matrix.trace B.val/2)*hAxisSignedSine B (.circle 0 s hs)
  change 0< -x*R.tangentSign at ha
  change 0< -y*S.tangentSign at hb
  change (if 0≤x*y*hAxisPairing (.circle 0 r hr) (.circle 0 s hs) then (1:ℝ) else -1)=
    R.tangentSign*S.tangentSign
  rcases hRsg with hRsg | hRsg <;> rcases hSsg with hSsg | hSsg
  all_goals rw [hRsg] at ha
  all_goals rw [hSsg] at hb
  all_goals rw [hRsg,hSsg]
  · have hprod:=mul_pos (mul_pos_of_neg_of_neg (by linarith : x<0) (by linarith : y<0)) hp
    rw [ite_eq_left hprod.le]
    norm_num
  · have hprod:=mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith : x<0) (by linarith : 0<y)) hp
    rw [ite_eq_right hprod.not_ge]
    norm_num
  · have hprod:=mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith : 0<x) (by linarith : y<0)) hp
    rw [ite_eq_right hprod.not_ge]
    norm_num
  · have hprod:=mul_pos (mul_pos (by linarith : 0<x) (by linarith : 0<y)) hp
    rw [ite_eq_left hprod.le]
    norm_num


/-- At concentric apices, the actual Euclidean forward tangents have their literal signed product. -/
theorem hConcentric_forward_tangent_inner (r s : ℝ) (hr : 0<r) (hs : 0<s)
    (R : HRayAt (metricProbe 0 r hr)) (S : HRayAt (metricProbe 0 s hs))
    (hR : R.supportLine=.circle 0 r hr) (hS : S.supportLine=.circle 0 s hs) :
    inner ℝ R.tangentVector S.tangentVector=(r*s)*(R.tangentSign*S.tangentSign) := by
  simp [HRayAt.tangentVector,hR,hS,HalfPlaneLine.tangentAt,
    metricProbe,Complex.mul_re,Complex.mul_im]
  ring

/-- The relative matrix sign is the actual same/opposite direction of the two forward tangent arrows. -/
theorem hRelativeAxisSign_concentric_eq_direction
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (r s : ℝ) (hr : 0<r) (hs : 0<s)
    (haxisA : hHyperbolicAxis A hA htA=.circle 0 r hr)
    (haxisB : hHyperbolicAxis B hB htB=.circle 0 s hs)
    (R : HRayAt (metricProbe 0 r hr)) (S : HRayAt (metricProbe 0 s hs))
    (hR : Mobius.MobiusAttractiveFixedPoint (realSLMobius A) R.idealEndpoint)
    (hS : Mobius.MobiusAttractiveFixedPoint (realSLMobius B) S.idealEndpoint) :
    hRelativeAxisSign A B (.circle 0 r hr) (.circle 0 s hs)=
      if 0 < inner ℝ R.tangentVector S.tangentVector then 1 else -1 := by
  have hRL:=(hHyperbolic_concentric_attractive_direction A hA htA r hr haxisA R hR).1
  have hSM:=(hHyperbolic_concentric_attractive_direction B hB htB s hs haxisB S hS).1
  rw [hRelativeAxisSign_concentric_attractive A B hA hB htA htB r s hr hs haxisA haxisB R S hR hS]
  have hsq : (R.tangentSign*S.tangentSign)^2=1 := by
    rw [mul_pow,R.tangentSign_sq,S.tangentSign_sq]
    norm_num
  have hpos : 0<R.tangentSign*S.tangentSign ↔ 0 < inner ℝ R.tangentVector S.tangentVector := by
    rw [hConcentric_forward_tangent_inner r s hr hs R S hRL hSM]
    exact (mul_pos_iff_of_pos_left (mul_pos hr hs)).symm
  split_ifs with h
  · have hh:=hpos.mpr h
    nlinarith
  · have hh : R.tangentSign*S.tangentSign≤0 := le_of_not_gt (fun he=>h (hpos.mp he))
    nlinarith

/-- Real conjugation preserves nontriviality of the original geometric transformation. -/
theorem hSL_nontrivial_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) : realSLMobius (q*A*q⁻¹)≠1 := by
  intro he
  have hh:=congrArg (fun x:Mobius.complexMobiusGroup=>(realSLMobius q)⁻¹*x*realSLMobius q) he
  apply hA
  simpa [map_mul,map_inv,mul_assoc] using hh

/-- A genuine axis transports to the genuine axis of the conjugated transformation. -/
theorem hHyperbolicAxis_conjugation (A q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A≠1) (ht : 4 < (Matrix.trace A.val)^2) :
    hHyperbolicAxis (q*A*q⁻¹) (hSL_nontrivial_conjugation A q hA)
      (by rwa [hSL_trace_conjugation])=
      (hHyperbolicAxis A hA ht).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q) := by
  apply Eq.symm
  apply hHyperbolicAxis_unique_invariant
  rw [HalfPlaneLine.realGLMap_carrier]
  change (fun z:ℍ=>(q*A*q⁻¹)•z) '' ((fun z:ℍ=>q•z) '' (hHyperbolicAxis A hA ht).carrier)=
    (fun z:ℍ=>q•z) '' (hHyperbolicAxis A hA ht).carrier
  rw [←Set.image_comp]
  have he : (fun z:ℍ=>(q*A*q⁻¹)•z) ∘ (fun z:ℍ=>q•z)=
      (fun z:ℍ=>q•z) ∘ (fun z:ℍ=>A•z) := by
    funext z
    simp [mul_smul]
  rw [he,Set.image_comp,hHyperbolicAxis_invariant]

/-- The relative sign is invariant under genuine simultaneous real conjugation. -/
theorem hRelativeAxisSign_conjugation
    (A B q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M L' M' : HalfPlaneLine)
    (hL : ∀p∈L.idealEndpoints,(realSLMobius A).val p=p)
    (hM : ∀p∈M.idealEndpoints,(realSLMobius B).val p=p)
    (hL' : ∀p∈L'.idealEndpoints,(realSLMobius (q*A*q⁻¹)).val p=p)
    (hM' : ∀p∈M'.idealEndpoints,(realSLMobius (q*B*q⁻¹)).val p=p) :
    hRelativeAxisSign (q*A*q⁻¹) (q*B*q⁻¹) L' M'=hRelativeAxisSign A B L M := by
  have h:=hSL_product_trace_axis_pairing A B L M hL hM
  have h':=hSL_product_trace_axis_pairing (q*A*q⁻¹) (q*B*q⁻¹) L' M' hL' hM'
  rw [show (q*A*q⁻¹)*(q*B*q⁻¹)=q*(A*B)*q⁻¹ by group,
    hSL_trace_conjugation,hSL_trace_conjugation,hSL_trace_conjugation] at h'
  have he : hAxisSignedSine (q*A*q⁻¹) L'*hAxisSignedSine (q*B*q⁻¹) M'*hAxisPairing L' M'=
      hAxisSignedSine A L*hAxisSignedSine B M*hAxisPairing L M := by
    dsimp only [hAxisPairing]
    linarith
  unfold hRelativeAxisSign
  rw [hSL_trace_conjugation,hSL_trace_conjugation,he]

/-- An attractive actual ray exists from every actual point on a hyperbolic axis. -/
theorem hHyperbolic_attractive_ray_exists
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1)
    (ht : 4 < (Matrix.trace A.val)^2) (p : ℍ) (hp : p∈(hHyperbolicAxis A hA ht).carrier) :
    ∃R:HRayAt p,Mobius.MobiusAttractiveFixedPoint (realSLMobius A) R.idealEndpoint := by
  obtain ⟨w,⟨_,hAw,hT⟩,_⟩:=realSL_hyperbolic_halfturn_factor A hA ht p hp
  have hpw : p≠w := by
    intro he
    rw [←he,dist_self,mul_zero] at hT
    have hh:=hHyperbolic_translationLength_pos A hA ht
    linarith
  exact ⟨hRayThrough p w hpw,realSL_hyperbolic_halfturn_ray_attractive A hA ht p w hpw hp hAw⟩

/-- The source relative direction is measured by the genuine attractive tangent arrows
at the two apices after a genuine concentric-axis normalization. -/
def HasHRelativeAttractiveDirection
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (L M : HalfPlaneLine) (ε : ℝ) : Prop :=
  ∃ (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (r s : ℝ) (hr : 0<r) (hs : 0<s),
    L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=.circle 0 r hr ∧
    M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q)=.circle 0 s hs ∧
    ∃ (R : HRayAt (metricProbe 0 r hr)) (S : HRayAt (metricProbe 0 s hs)),
      Mobius.MobiusAttractiveFixedPoint (realSLMobius (q*A*q⁻¹)) R.idealEndpoint ∧
      Mobius.MobiusAttractiveFixedPoint (realSLMobius (q*B*q⁻¹)) S.idealEndpoint ∧
      ε=(if 0 < inner ℝ R.tangentVector S.tangentVector then 1 else -1)


/-- The geometric attractive-arrow definition agrees with the intrinsic sign;
in particular it is independent of every chosen concentric normalizer and ray witness. -/
theorem HasHRelativeAttractiveDirection.eq_intrinsic
    {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2) {ε : ℝ}
    (hdir : HasHRelativeAttractiveDirection A B (hHyperbolicAxis A hA htA) (hHyperbolicAxis B hB htB) ε) :
    ε=hRelativeAxisSign A B (hHyperbolicAxis A hA htA) (hHyperbolicAxis B hB htB) := by
  obtain ⟨q,r,s,hr,hs,hL,hM,R,S,hR,hS,rfl⟩:=hdir
  let Aq:=q*A*q⁻¹
  let Bq:=q*B*q⁻¹
  have hAq : realSLMobius Aq≠1:=hSL_nontrivial_conjugation A q hA
  have hBq : realSLMobius Bq≠1:=hSL_nontrivial_conjugation B q hB
  have htAq : 4 < (Matrix.trace Aq.val)^2 := by dsimp only [Aq];rwa [hSL_trace_conjugation]
  have htBq : 4 < (Matrix.trace Bq.val)^2 := by dsimp only [Bq];rwa [hSL_trace_conjugation]
  have haxisAq : hHyperbolicAxis Aq hAq htAq=.circle 0 r hr := by
    rw [hHyperbolicAxis_conjugation]
    exact hL
  have haxisBq : hHyperbolicAxis Bq hBq htBq=.circle 0 s hs := by
    rw [hHyperbolicAxis_conjugation]
    exact hM
  have hLf : ∀p∈(hHyperbolicAxis A hA htA).idealEndpoints,(realSLMobius A).val p=p := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hMf : ∀p∈(hHyperbolicAxis B hB htB).idealEndpoints,(realSLMobius B).val p=p := by
    rw [hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hLf' : ∀p∈(HalfPlaneLine.circle 0 r hr).idealEndpoints,(realSLMobius Aq).val p=p := by
    rw [←haxisAq,hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hMf' : ∀p∈(HalfPlaneLine.circle 0 s hs).idealEndpoints,(realSLMobius Bq).val p=p := by
    rw [←haxisBq,hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  exact (hRelativeAxisSign_concentric_eq_direction Aq Bq hAq hBq htAq htBq r s hr hs
    haxisAq haxisBq R S hR hS).symm.trans
      (hRelativeAxisSign_conjugation A B q _ _ _ _ hLf hMf hLf' hMf')

/-- Every genuinely disjoint pair has an actual attractive-arrow direction. -/
theorem hHyperbolic_relative_attractive_direction_exists
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hdis : (hHyperbolicAxis A hA htA).HDisjoint (hHyperbolicAxis B hB htB)) :
    ∃ε:ℝ,HasHRelativeAttractiveDirection A B (hHyperbolicAxis A hA htA) (hHyperbolicAxis B hB htB) ε := by
  obtain ⟨q,r,s,hr,hs,_,hL,hM⟩:=(hHyperbolicAxis A hA htA).disjoint_SL_normalizer _ hdis
  let Aq:=q*A*q⁻¹
  let Bq:=q*B*q⁻¹
  have hAq : realSLMobius Aq≠1:=hSL_nontrivial_conjugation A q hA
  have hBq : realSLMobius Bq≠1:=hSL_nontrivial_conjugation B q hB
  have htAq : 4 < (Matrix.trace Aq.val)^2 := by dsimp only [Aq];rwa [hSL_trace_conjugation]
  have htBq : 4 < (Matrix.trace Bq.val)^2 := by dsimp only [Bq];rwa [hSL_trace_conjugation]
  have haxisAq : hHyperbolicAxis Aq hAq htAq=.circle 0 r hr := by
    rw [hHyperbolicAxis_conjugation]
    exact hL
  have haxisBq : hHyperbolicAxis Bq hBq htBq=.circle 0 s hs := by
    rw [hHyperbolicAxis_conjugation]
    exact hM
  have hpA : metricProbe 0 r hr∈(hHyperbolicAxis Aq hAq htAq).carrier := by
    rw [haxisAq]
    change ‖((metricProbe 0 r hr:ℍ):ℂ)-(0:ℂ)‖=r
    simp [metricProbe,Complex.norm_def]
    exact Real.sqrt_mul_self hr.le
  have hpB : metricProbe 0 s hs∈(hHyperbolicAxis Bq hBq htBq).carrier := by
    rw [haxisBq]
    change ‖((metricProbe 0 s hs:ℍ):ℂ)-(0:ℂ)‖=s
    simp [metricProbe,Complex.norm_def]
    exact Real.sqrt_mul_self hs.le
  obtain ⟨R,hR⟩:=hHyperbolic_attractive_ray_exists Aq hAq htAq _ hpA
  obtain ⟨S,hS⟩:=hHyperbolic_attractive_ray_exists Bq hBq htBq _ hpB
  exact ⟨_,q,r,s,hr,hs,hL,hM,R,S,hR,hS,rfl⟩

/-- The relative direction is genuinely geometric, uniquely defined, and exactly one of the two arrows signs. -/
theorem hHyperbolic_relative_attractive_direction_unique
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hdis : (hHyperbolicAxis A hA htA).HDisjoint (hHyperbolicAxis B hB htB)) :
    ∃!ε:ℝ,HasHRelativeAttractiveDirection A B (hHyperbolicAxis A hA htA) (hHyperbolicAxis B hB htB) ε := by
  obtain ⟨ε,hε⟩:=hHyperbolic_relative_attractive_direction_exists A B hA hB htA htB hdis
  exact ⟨ε,hε,fun η hη=>(hη.eq_intrinsic hA hB htA htB).trans (hε.eq_intrinsic hA hB htA htB).symm⟩

/-- With the actual same/opposite attractive tangent directions, independent of all lifts and charts. -/
theorem hHyperbolic_product_abs_trace_relative_direction
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hdis : (hHyperbolicAxis A hA htA).HDisjoint (hHyperbolicAxis B hB htB)) (ε : ℝ)
    (hdir : HasHRelativeAttractiveDirection A B (hHyperbolicAxis A hA htA) (hHyperbolicAxis B hB htB) ε) :
    |Matrix.trace (A*B).val|/2=
      |ε*Real.cosh ((hHyperbolicAxis A hA htA).lineDist (hHyperbolicAxis B hB htB))*
        Real.sinh (hTranslationLength (hSLIsometry A)/2)*Real.sinh (hTranslationLength (hSLIsometry B)/2)+
        Real.cosh (hTranslationLength (hSLIsometry A)/2)*Real.cosh (hTranslationLength (hSLIsometry B)/2)| := by
  have h:=hHyperbolic_product_abs_trace_disjoint A B hA hB htA htB hdis
  dsimp only at h
  rw [←hdir.eq_intrinsic hA hB htA htB] at h
  exact h

/--
The product of disjoint-axis hyperbolic transformations with the same
actual attractive-arrow direction is genuinely hyperbolic.
-/
theorem hHyperbolic_product_same_attractive_direction
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A≠1) (hB : realSLMobius B≠1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hdis : (hHyperbolicAxis A hA htA).HDisjoint (hHyperbolicAxis B hB htB))
    (hdir : HasHRelativeAttractiveDirection A B (hHyperbolicAxis A hA htA) (hHyperbolicAxis B hB htB) 1) :
    Mobius.MobiusHyperbolic (realSLMobius (A*B)) := by
  have h:=hHyperbolic_product_abs_trace_relative_direction A B hA hB htA htB hdis 1 hdir
  rw [one_mul] at h
  have hsA : 0<Real.sinh (hTranslationLength (hSLIsometry A)/2) :=
    Real.sinh_pos_iff.mpr (by linarith [hHyperbolic_translationLength_pos A hA htA])
  have hsB : 0<Real.sinh (hTranslationLength (hSLIsometry B)/2) :=
    Real.sinh_pos_iff.mpr (by linarith [hHyperbolic_translationLength_pos B hB htB])
  have hpos:=mul_pos (mul_pos (Real.cosh_pos
    ((hHyperbolicAxis A hA htA).lineDist (hHyperbolicAxis B hB htB))) hsA) hsB
  have hone : 1≤Real.cosh (hTranslationLength (hSLIsometry A)/2)*
      Real.cosh (hTranslationLength (hSLIsometry B)/2) :=
    by
      have hcA:=Real.one_le_cosh (hTranslationLength (hSLIsometry A)/2)
      have hcB:=Real.one_le_cosh (hTranslationLength (hSLIsometry B)/2)
      nlinarith [mul_nonneg (sub_nonneg.mpr hcA) (sub_nonneg.mpr hcB)]
  have hgt : 1<Real.cosh ((hHyperbolicAxis A hA htA).lineDist (hHyperbolicAxis B hB htB))*
      Real.sinh (hTranslationLength (hSLIsometry A)/2)*Real.sinh (hTranslationLength (hSLIsometry B)/2)+
      Real.cosh (hTranslationLength (hSLIsometry A)/2)*Real.cosh (hTranslationLength (hSLIsometry B)/2) := by linarith
  rw [abs_of_pos (lt_trans zero_lt_one hgt)] at h
  exact hSL_hyperbolic_of_two_lt_abs_trace (A*B) (by linarith)


/-- Genuine relative attractive directions have exactly the two source values. -/
theorem HasHRelativeAttractiveDirection.eq_one_or_neg_one
    {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} {L M : HalfPlaneLine} {ε : ℝ}
    (hdir : HasHRelativeAttractiveDirection A B L M ε) : ε=1 ∨ ε= -1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,rfl⟩:=hdir
  split_ifs <;> simp

end LowDimensionalTopology.Geometry.Hyperbolic
