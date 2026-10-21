/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Hyperboloid line element and path metric

Lengths range over all finite chains of ambient continuously differentiable curves in the positive Lorentz sheet.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Coordinates

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace ContDiff Manifold ENNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

def hyperboloidProjectTangent (x : Hyperboloid n) (v : LorentzVector n) : Inversive.Euclidean n :=
  (1+x.val.1)⁻¹ • v.2 - (v.1/(1+x.val.1)^2) • x.val.2

theorem hyperboloidProjectTangent_norm_sq (x : Hyperboloid n) (v : LorentzVector n)
    (hv : HyperboloidTangent x v) :
    ‖hyperboloidProjectTangent x v‖^2=(-lorentzForm v v)/(1+x.val.1)^2 := by
  have ht : 0<1+x.val.1 := by linarith [x.property.2]
  have horth : inner ℝ v.2 x.val.2=x.val.1*v.1 := by
    have h:=hv
    unfold HyperboloidTangent lorentzForm at h
    rw [real_inner_comm] at h
    linarith
  rw [hyperboloidProjectTangent,norm_sub_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_left,inner_smul_right,
    RCLike.conj_to_real,horth]
  rw [lorentzForm_self]
  have he := congrArg (fun t : ℝ => t*v.1^2) (hyperboloid_time_sq x)
  field_simp [ht.ne']
  nlinarith only [he]

theorem hyperboloidProject_density (x : Hyperboloid n) :
    ballDensity n (hyperboloidProject x)=1+x.val.1 := by
  change 2/(1-‖hyperboloidProjectRaw x.val‖^2)=1+x.val.1
  rw [hyperboloidProjectRaw_norm_sq]
  have ht : 0<x.val.1+1 := by linarith [x.property.2]
  have hd : 0<1-(x.val.1-1)/(x.val.1+1) :=
    sub_pos.mpr ((div_lt_one ht).mpr (by linarith))
  field_simp [hd.ne',ht.ne']
  ring

theorem hyperboloidProject_speed_covariance (x : Hyperboloid n) (v : LorentzVector n)
    (hv : HyperboloidTangent x v) :
    ballDensity n (hyperboloidProject x)*‖hyperboloidProjectTangent x v‖=hyperboloidLineElement v := by
  have ht : 0<1+x.val.1 := by linarith [x.property.2]
  have hs : (ballDensity n (hyperboloidProject x)*‖hyperboloidProjectTangent x v‖)^2=
      (hyperboloidLineElement v)^2 := by
    rw [hyperboloidProject_density,mul_pow,hyperboloidProjectTangent_norm_sq x v hv,
      hyperboloidLineElement_sq x v hv,lorentzForm_self]
    field_simp [ht.ne']
    ring
  exact (sq_eq_sq₀ (mul_nonneg ((ballDensity n).positive (hyperboloidProject x)).le (norm_nonneg _))
    (Real.sqrt_nonneg _)).mp hs

theorem hyperboloid_curve_tangentWithin {γ : ℝ → Hyperboloid n} {v : LorentzVector n}
    {s : Set ℝ} {t : ℝ} (hc : HasDerivWithinAt (fun u => (γ u).val) v s t)
    (hu : UniqueDiffWithinAt ℝ s t) : HyperboloidTangent (γ t) v := by
  have ht : HasDerivWithinAt (fun u => (γ u).val.1) v.1 s t := by
    simpa using hc.hasFDerivWithinAt.fst.hasDerivWithinAt
  have hs : HasDerivWithinAt (fun u => (γ u).val.2) v.2 s t := by
    simpa using hc.hasFDerivWithinAt.snd.hasDerivWithinAt
  have hd := (ht.mul ht).sub (hs.inner ℝ hs)
  have hz := hd.congr (f₁ := fun _ => (1 : ℝ))
    (fun u _ => (γ u).property.1.symm) (γ t).property.1.symm
  have he := UniqueDiffWithinAt.eq_deriv s hu hz (hasDerivWithinAt_const t s (1 : ℝ))
  unfold HyperboloidTangent lorentzForm
  nlinarith [real_inner_comm (γ t).val.2 v.2]

theorem hyperboloidProject_hasDerivWithinAt {γ : ℝ → Hyperboloid n} {v : LorentzVector n}
    {s : Set ℝ} {t : ℝ} (hc : HasDerivWithinAt (fun u => (γ u).val) v s t) :
    HasDerivWithinAt (fun u => (hyperboloidProject (γ u)).val)
      (hyperboloidProjectTangent (γ t) v) s t := by
  have ht : HasDerivWithinAt (fun u => (γ u).val.1) v.1 s t := by
    simpa using hc.hasFDerivWithinAt.fst.hasDerivWithinAt
  have hs : HasDerivWithinAt (fun u => (γ u).val.2) v.2 s t := by
    simpa using hc.hasFDerivWithinAt.snd.hasDerivWithinAt
  have hi := ((hasDerivWithinAt_const t s (1 : ℝ)).add ht).inv (by
    have h:0<1+(γ t).val.1 := by linarith [(γ t).property.2]
    exact h.ne')
  convert hi.smul hs using 1
  · rfl
  · dsimp [hyperboloidProjectTangent]
    rw [neg_div,neg_smul]
    abel_nf

theorem ball_contMDiffOn_of_ambient {γ : ℝ → unitBallDomain n} {s : Set ℝ}
    (hc : ContDiffOn ℝ 1 (fun t => (γ t).val) s) :
    ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,Inversive.Euclidean n) 1 γ s := by
  intro t ht
  rw [contMDiffWithinAt_iff_target]
  constructor
  · exact Topology.IsEmbedding.subtypeVal.isInducing.tendsto_nhds_iff.mpr (hc.continuousOn t ht)
  · rw [contMDiffWithinAt_iff_contDiffWithinAt]
    simpa only [extChartAt,TopologicalSpace.Opens.chartAt_eq,mfld_simps,Set.domRestrict,Function.comp_def] using hc t ht

theorem hyperboloidProject_contMDiffOn {γ : ℝ → Hyperboloid n} {s : Set ℝ}
    (hc : ContDiffOn ℝ 1 (fun t => (γ t).val) s) :
    ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,Inversive.Euclidean n) 1 (fun t => hyperboloidProject (γ t)) s := by
  apply ball_contMDiffOn_of_ambient
  have hh := ((contDiffOn_const.add hc.fst).inv (fun t _ => by
    have h:0<1+(γ t).val.1 := by linarith [(γ t).property.2]
    exact h.ne')).smul hc.snd
  exact hh

theorem ballHyperboloid_contDiffOn {γ : ℝ → unitBallDomain n} {s : Set ℝ}
    (hc : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,Inversive.Euclidean n) 1 γ s) :
    ContDiffOn ℝ 1 (fun t => (ballHyperboloid (γ t)).val) s := by
  have ha := Auxiliary.Analysis.openDomain_contDiffOn_ambient hc
  have hn := ha.norm_sq ℝ
  have hd : ContDiffOn ℝ 1 (fun t => 1-‖(γ t).val‖^2) s := contDiffOn_const.sub hn
  have hne : ∀ t∈s,1-‖(γ t).val‖^2≠0 := by
    intro t _
    have hp := unitBallDomain_norm_lt (γ t)
    have hn0 := norm_nonneg (γ t).val
    have h:0<1-‖(γ t).val‖^2 := by nlinarith
    exact h.ne'
  change ContDiffOn ℝ 1 (fun t => ((1+‖(γ t).val‖^2)/(1-‖(γ t).val‖^2),
    (2/(1-‖(γ t).val‖^2)) • (γ t).val)) s
  exact ((contDiffOn_const.add hn).div hd hne).prodMk
    ((contDiffOn_const.div hd hne).smul ha)

def hyperboloidPieceELength (γ : ℝ → Hyperboloid n) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ENNReal.ofReal (hyperboloidLineElement
    (derivWithin (fun u => (γ u).val) (Icc a b) t))

inductive HyperboloidC1Chain (n : ℕ) : Hyperboloid n → Hyperboloid n → Type where
  | nil (x : Hyperboloid n) : HyperboloidC1Chain n x x
  | cons {x y z : Hyperboloid n} (γ : ℝ → Hyperboloid n) (a b : ℝ) (hab : a≤b)
      (hc : ContDiffOn ℝ 1 (fun t => (γ t).val) (Icc a b)) (ha : γ a=x) (hb : γ b=y)
      (tail : HyperboloidC1Chain n y z) : HyperboloidC1Chain n x z

def HyperboloidC1Chain.length {x y : Hyperboloid n} : HyperboloidC1Chain n x y → ℝ≥0∞
  | .nil _ => 0
  | .cons γ a b _ _ _ _ tail => hyperboloidPieceELength γ a b + tail.length

def HyperboloidC1Chain.project {x y : Hyperboloid n} : HyperboloidC1Chain n x y →
    Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ,Inversive.Euclidean n) (unitBallDomain n)
      (hyperboloidProject x) (hyperboloidProject y)
  | .nil _ => .nil _
  | .cons γ a b hab hc ha hb tail => .cons (fun t => hyperboloidProject (γ t)) a b hab
      (hyperboloidProject_contMDiffOn hc) (congrArg hyperboloidProject ha)
      (congrArg hyperboloidProject hb) tail.project

theorem hyperboloidProject_pieceLength (γ : ℝ → Hyperboloid n) (a b : ℝ) (hab : a≤b)
    (hc : ContDiffOn ℝ 1 (fun t => (γ t).val) (Icc a b)) :
    (ballDensity n).pieceLength (fun t => hyperboloidProject (γ t)) a b=
      hyperboloidPieceELength γ a b := by
  rw [(ballDensity n).pieceLength_eq_lintegral _ _ _ (hyperboloidProject_contMDiffOn hc)]
  rcases hab.eq_or_lt with rfl | hab
  · simp [hyperboloidPieceELength]
  unfold hyperboloidPieceELength
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  have hu := uniqueDiffOn_Icc hab t ht
  have hd := (hc.differentiableOn one_ne_zero t ht).hasDerivWithinAt
  rw [(hyperboloidProject_hasDerivWithinAt hd).derivWithin hu]
  exact congrArg ENNReal.ofReal (hyperboloidProject_speed_covariance (γ t) _
    (hyperboloid_curve_tangentWithin hd hu))

theorem HyperboloidC1Chain.project_length {x y : Hyperboloid n} (c : HyperboloidC1Chain n x y) :
    (ballDensity n).chainLength c.project=c.length := by
  induction c with
  | nil x => rfl
  | cons γ a b hab hc ha hb tail ih =>
    change (ballDensity n).pieceLength (fun t => hyperboloidProject (γ t)) a b +
      (ballDensity n).chainLength tail.project=hyperboloidPieceELength γ a b+tail.length
    rw [hyperboloidProject_pieceLength γ a b hab hc,ih]

def hyperboloidLiftChain {x y : unitBallDomain n} :
    Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ,Inversive.Euclidean n) (unitBallDomain n) x y →
      HyperboloidC1Chain n (ballHyperboloid x) (ballHyperboloid y)
  | .nil _ => .nil _
  | .cons γ a b hab hc ha hb tail => .cons (fun t => ballHyperboloid (γ t)) a b hab
      (ballHyperboloid_contDiffOn hc) (congrArg ballHyperboloid ha)
      (congrArg ballHyperboloid hb) (hyperboloidLiftChain tail)

theorem hyperboloidLiftChain_length {x y : unitBallDomain n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ,Inversive.Euclidean n) (unitBallDomain n) x y) :
    (hyperboloidLiftChain c).length=(ballDensity n).chainLength c := by
  induction c with
  | nil x => rfl
  | cons γ a b hab hc ha hb tail ih =>
    have hfun : (fun t => hyperboloidProject (ballHyperboloid (γ t)))=γ := by
      funext t
      exact hyperboloidProject_ballHyperboloid (γ t)
    have hp := hyperboloidProject_pieceLength (fun t => ballHyperboloid (γ t)) a b hab
      (ballHyperboloid_contDiffOn hc)
    rw [hfun] at hp
    change hyperboloidPieceELength (fun t => ballHyperboloid (γ t)) a b+
      (hyperboloidLiftChain tail).length=(ballDensity n).pieceLength γ a b+
        (ballDensity n).chainLength tail
    rw [← hp,ih]

def hyperboloidPathEDist (x y : Hyperboloid n) : ℝ≥0∞ :=
  ⨅ c : HyperboloidC1Chain n x y,c.length

theorem ball_pathEDist_le_hyperboloidPathEDist (x y : Hyperboloid n) :
    (ballDensity n).pathEDist (hyperboloidProject x) (hyperboloidProject y)≤hyperboloidPathEDist x y := by
  apply le_iInf
  intro c
  have h : (ballDensity n).pathEDist (hyperboloidProject x) (hyperboloidProject y)≤
      (ballDensity n).chainLength c.project := by
    rw [(ballDensity n).pathEDist_eq_piecewiseEDist]
    exact iInf_le _ c.project
  exact h.trans_eq c.project_length

theorem hyperboloidPathEDist_eq_ballPathEDist (x y : Hyperboloid n) :
    hyperboloidPathEDist x y=(ballDensity n).pathEDist (hyperboloidProject x) (hyperboloidProject y) := by
  apply le_antisymm
  · have h : hyperboloidPathEDist (ballHyperboloid (hyperboloidProject x))
        (ballHyperboloid (hyperboloidProject y))≤
        (ballDensity n).pathEDist (hyperboloidProject x) (hyperboloidProject y) := by
      rw [(ballDensity n).pathEDist_eq_piecewiseEDist]
      apply le_iInf
      intro c
      exact (iInf_le _ (hyperboloidLiftChain c)).trans_eq (hyperboloidLiftChain_length c)
    simpa only [ballHyperboloid_hyperboloidProject] using h
  · exact ball_pathEDist_le_hyperboloidPathEDist x y

def hyperboloidPathDist (x y : Hyperboloid n) : ℝ := (hyperboloidPathEDist x y).toReal

abbrev hyperboloidMetricSpace (n : ℕ) : MetricSpace (Hyperboloid n) := by
  let : MetricSpace (unitBallDomain n) := ballMetricSpace n
  exact (hyperboloidBallHomeomorph n).isEmbedding.comapMetricSpace _

theorem hyperboloidMetricSpace_topology (n : ℕ) :
    (hyperboloidMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace=
      (inferInstance : TopologicalSpace (Hyperboloid n)) := rfl

theorem hyperboloidMetricSpace_dist (x y : Hyperboloid n) :
    @dist (Hyperboloid n) (hyperboloidMetricSpace n).toDist x y=hyperboloidPathDist x y := by
  change @dist (unitBallDomain n) (ballMetricSpace n).toDist
    (hyperboloidProject x) (hyperboloidProject y)=_
  rw [ballMetricSpace_dist]
  unfold hyperboloidPathDist
  rw [hyperboloidPathEDist_eq_ballPathEDist]
  rfl

theorem hyperboloidProject_isometry (n : ℕ) :
    @Isometry (Hyperboloid n) (unitBallDomain n)
      (hyperboloidMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
      (ballMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace (hyperboloidBallHomeomorph n) := by
  apply @Isometry.of_dist_eq (Hyperboloid n) (unitBallDomain n)
    (hyperboloidMetricSpace n).toPseudoMetricSpace (ballMetricSpace n).toPseudoMetricSpace
    (hyperboloidBallHomeomorph n)
  intro x y
  change @dist (unitBallDomain n) (ballMetricSpace n).toDist (hyperboloidProject x)
    (hyperboloidProject y)=@dist (Hyperboloid n) (hyperboloidMetricSpace n).toDist x y
  rw [ballMetricSpace_dist,hyperboloidMetricSpace_dist]
  unfold hyperboloidPathDist
  rw [hyperboloidPathEDist_eq_ballPathEDist]
  rfl

theorem hyperboloidPathDist_eq_ballPathDist (x y : Hyperboloid n) :
    hyperboloidPathDist x y=(ballDensity n).pathDist (hyperboloidProject x) (hyperboloidProject y) :=
  congrArg ENNReal.toReal (hyperboloidPathEDist_eq_ballPathEDist x y)

theorem HyperboloidC1Chain.length_ne_top {x y : Hyperboloid n} (c : HyperboloidC1Chain n x y) :
    c.length≠⊤ := by
  rw [← c.project_length]
  exact (ballDensity n).chainLength_ne_top c.project

theorem hyperboloidPathEDist_ne_top (x y : Hyperboloid n) : hyperboloidPathEDist x y≠⊤ := by
  rw [hyperboloidPathEDist_eq_ballPathEDist]
  exact (ballDensity n).pathEDist_ne_top _ _

theorem hyperboloidPathDist_eq_sInf_chain_lengths (x y : Hyperboloid n) :
    hyperboloidPathDist x y=sInf (range (fun c : HyperboloidC1Chain n x y => c.length.toReal)) := by
  have hb : BddBelow (range (fun c : HyperboloidC1Chain n x y => c.length.toReal)) :=
    ⟨0,by rintro _ ⟨c,rfl⟩; exact ENNReal.toReal_nonneg⟩
  have happrox {r : ℝ} (hr : hyperboloidPathDist x y<r) :
      ∃ c : HyperboloidC1Chain n x y,c.length.toReal<r := by
    have he : hyperboloidPathEDist x y<ENNReal.ofReal r :=
      (ENNReal.lt_ofReal_iff_toReal_lt (hyperboloidPathEDist_ne_top x y)).mpr hr
    rw [hyperboloidPathEDist,iInf_lt_iff] at he
    obtain ⟨c,hc⟩ := he
    exact ⟨c,(ENNReal.lt_ofReal_iff_toReal_lt c.length_ne_top).mp hc⟩
  have hnonempty : (range (fun c : HyperboloidC1Chain n x y => c.length.toReal)).Nonempty := by
    obtain ⟨c,_⟩ := happrox (show hyperboloidPathDist x y<hyperboloidPathDist x y+1 by linarith)
    exact ⟨_,c,rfl⟩
  apply le_antisymm
  · apply le_csInf hnonempty
    rintro _ ⟨c,rfl⟩
    exact ENNReal.toReal_mono c.length_ne_top (iInf_le _ c)
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨c,hc⟩ := happrox hr
    exact (csInf_le hb (mem_range_self c)).trans_lt hc

end LowDimensionalTopology.Geometry.Hyperbolic
