/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.CommonOrthogonals

/-!
# Genuine infimal line-line distance and its actual minimizing segment
-/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

theorem concentric_pointDist_minimizes (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (p z : ℍ) (hp0 : p.re=0) (hp : ‖(p : ℂ)‖=s) (hz : ‖(z : ℂ)‖=s) :
    (HalfPlaneLine.circle 0 t ht).pointDist p ≤ (HalfPlaneLine.circle 0 t ht).pointDist z := by
  have hn := norm_sub_real_sq 0 p
  simp only [Complex.ofReal_zero,sub_zero,hp,hp0,zero_pow (by norm_num : 2 ≠ 0),zero_add] at hn
  have hpi : p.im=s := by nlinarith [p.im_pos]
  have hnz := norm_sub_real_sq 0 z
  simp only [Complex.ofReal_zero,sub_zero,hz] at hnz
  have hzi : z.im≤s := by nlinarith [z.im_pos,sq_nonneg z.re]
  apply Real.sinh_le_sinh.mp
  rw [circleLine_pointDist_sinh,circleLine_pointDist_sinh]
  simp only [Complex.ofReal_zero,sub_zero,hp,hz,hpi]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by nlinarith)

theorem concentric_commonOrthogonal_dist_le (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (p q z w : ℍ) (hp0 : p.re=0) (hq0 : q.re=0)
    (hp : p ∈ (HalfPlaneLine.circle 0 s hs).carrier)
    (hq : q ∈ (HalfPlaneLine.circle 0 t ht).carrier)
    (hz : z ∈ (HalfPlaneLine.circle 0 s hs).carrier)
    (hw : w ∈ (HalfPlaneLine.circle 0 t ht).carrier) : dist p q ≤ dist z w := by
  have ho : (HalfPlaneLine.circle 0 t ht).OrthogonalAt (HalfPlaneLine.vertical 0) q :=
    ((HalfPlaneLine.circle 0 t ht).orthogonalAt_iff_coefficients (HalfPlaneLine.vertical 0) q hq hq0).mpr rfl
  have he := (HalfPlaneLine.circle 0 t ht).pointDist_eq_dist_of_perpendicular _ q p ho hp0
  have hp' : ‖(p : ℂ)‖=s := by simpa only [HalfPlaneLine.carrier,Complex.ofReal_zero,sub_zero,mem_ofPred_eq] using hp
  have hz' : ‖(z : ℂ)‖=s := by simpa only [HalfPlaneLine.carrier,Complex.ofReal_zero,sub_zero,mem_ofPred_eq] using hz
  rw [← he]
  exact (concentric_pointDist_minimizes s t hs ht p z hp0 hp' hz').trans
    (Metric.infDist_le_dist_of_mem hw)

/-- The true common perpendicular realizes a global minimum among all actual pairs of line points. -/
theorem HalfPlaneLine.commonOrthogonal_dist_le (L M N : HalfPlaneLine) (p q z w : ℍ)
    (hp : L.OrthogonalAt N p) (hq : M.OrthogonalAt N q)
    (hz : z ∈ L.carrier) (hw : w ∈ M.carrier) : dist p q ≤ dist z w := by
  obtain ⟨g,_,hN⟩ := N.exists_mobius_map (HalfPlaneLine.vertical 0)
  obtain ⟨L',hL⟩ := realGL_image_hLine g L
  obtain ⟨M',hM⟩ := realGL_image_hLine g M
  have hp' := L.orthogonalAt_isometry_image N L' _ (g • ·) (realGL_isometry g) hL hN hp
  have hq' := M.orthogonalAt_isometry_image N M' _ (g • ·) (realGL_isometry g) hM hN hq
  have hLc := (L'.orthogonalAt_iff_coefficients _ _ hp'.1 hp'.2.1).mp hp'
  have hMc := (M'.orthogonalAt_iff_coefficients _ _ hq'.1 hq'.2.1).mp hq'
  cases L' with
  | vertical a => exact hLc.elim
  | circle a s hs =>
    change a=0 at hLc
    subst a
    cases M' with
    | vertical b => exact hMc.elim
    | circle b t ht =>
      change b=0 at hMc
      subst b
      have hz' : g • z ∈ (HalfPlaneLine.circle 0 s hs).carrier := hL ▸ mem_image_of_mem _ hz
      have hw' : g • w ∈ (HalfPlaneLine.circle 0 t ht).carrier := hM ▸ mem_image_of_mem _ hw
      have h := concentric_commonOrthogonal_dist_le s t hs ht (g • p) (g • q) (g • z) (g • w)
        hp'.2.1 hq'.2.1 hp'.1 hq'.1 hz' hw'
      simpa only [realGL_distance] using h

def HalfPlaneLine.pairDistances (L M : HalfPlaneLine) : Set ℝ :=
  {d | ∃ z ∈ L.carrier, ∃ w ∈ M.carrier, d=dist z w}

def HalfPlaneLine.lineDist (L M : HalfPlaneLine) : ℝ := sInf (L.pairDistances M)

theorem HalfPlaneLine.pairDistances_nonempty (L M : HalfPlaneLine) :
    (L.pairDistances M).Nonempty := by
  obtain ⟨z,_,hz,_,_⟩ := L.exists_two_points
  obtain ⟨w,_,hw,_,_⟩ := M.exists_two_points
  exact ⟨dist z w,z,hz,w,hw,rfl⟩

theorem HalfPlaneLine.pairDistances_bddBelow (L M : HalfPlaneLine) :
    BddBelow (L.pairDistances M) := by
  refine ⟨0,?_⟩
  rintro _ ⟨z,_,w,_,rfl⟩
  exact dist_nonneg

theorem HalfPlaneLine.lineDist_nonneg (L M : HalfPlaneLine) : 0≤L.lineDist M := by
  apply le_csInf (L.pairDistances_nonempty M)
  rintro _ ⟨z,_,w,_,rfl⟩
  exact dist_nonneg

theorem HalfPlaneLine.lineDist_le_dist (L M : HalfPlaneLine) {z w : ℍ}
    (hz : z ∈ L.carrier) (hw : w ∈ M.carrier) : L.lineDist M≤dist z w :=
  csInf_le (L.pairDistances_bddBelow M) ⟨z,hz,w,hw,rfl⟩

theorem HalfPlaneLine.lineDist_eq_commonOrthogonal (L M N : HalfPlaneLine) (p q : ℍ)
    (hp : L.OrthogonalAt N p) (hq : M.OrthogonalAt N q) : L.lineDist M=dist p q := by
  apply le_antisymm (L.lineDist_le_dist M hp.1 hq.1)
  apply le_csInf (L.pairDistances_nonempty M)
  rintro _ ⟨z,hz,w,hw,rfl⟩
  exact L.commonOrthogonal_dist_le M N p q z w hp hq hz hw

theorem HalfPlaneLine.exists_commonOrthogonal_minimum (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    ∃ (N : HalfPlaneLine) (p q : ℍ), L.OrthogonalAt N p ∧ M.OrthogonalAt N q ∧
      L.lineDist M=dist p q ∧ ∀ z ∈ L.carrier, ∀ w ∈ M.carrier, dist p q≤dist z w := by
  obtain ⟨N,⟨⟨p,hp⟩,⟨q,hq⟩⟩,_⟩ := L.existsUnique_commonOrthogonal M hd
  exact ⟨N,p,q,hp,hq,L.lineDist_eq_commonOrthogonal M N p q hp hq,
    fun z hz w hw => L.commonOrthogonal_dist_le M N p q z w hp hq hz hw⟩

def DiscLine.pairDistances (L M : DiscLine) : Set ℝ :=
  {d | ∃ z ∈ L.carrier, ∃ w ∈ M.carrier, d=discPathDist z w}

def DiscLine.lineDist (L M : DiscLine) : ℝ := sInf (L.pairDistances M)

theorem DiscLine.pairDistances_eq_halfPlane (L M : DiscLine) :
    L.pairDistances M=L.toHalfPlane.pairDistances M.toHalfPlane := by
  ext d
  constructor
  · rintro ⟨z,hz,w,hw,rfl⟩
    exact ⟨discToHalfPlane z,(L.mem_carrier z).mp hz,discToHalfPlane w,(M.mem_carrier w).mp hw,
      discPathDist_eq_halfPlane z w⟩
  · rintro ⟨z,hz,w,hw,rfl⟩
    refine ⟨halfPlaneToDisc z,?_,halfPlaneToDisc w,?_,?_⟩
    · rw [L.mem_carrier,discToHalfPlane_halfPlaneToDisc]
      exact hz
    · rw [M.mem_carrier,discToHalfPlane_halfPlaneToDisc]
      exact hw
    · rw [discPathDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc,discToHalfPlane_halfPlaneToDisc]

theorem DiscLine.lineDist_eq_halfPlane (L M : DiscLine) :
    L.lineDist M=L.toHalfPlane.lineDist M.toHalfPlane := by
  rw [DiscLine.lineDist,L.pairDistances_eq_halfPlane,HalfPlaneLine.lineDist]

theorem DiscLine.lineDist_nonneg (L M : DiscLine) : 0≤L.lineDist M := by
  rw [L.lineDist_eq_halfPlane]
  exact L.toHalfPlane.lineDist_nonneg M.toHalfPlane

theorem DiscLine.lineDist_le_dist (L M : DiscLine) {z w : 𝔻}
    (hz : z ∈ L.carrier) (hw : w ∈ M.carrier) : L.lineDist M≤discPathDist z w := by
  rw [L.lineDist_eq_halfPlane,discPathDist_eq_halfPlane]
  exact L.toHalfPlane.lineDist_le_dist M.toHalfPlane ((L.mem_carrier z).mp hz) ((M.mem_carrier w).mp hw)

theorem DiscLine.lineDist_eq_commonOrthogonal (L M N : DiscLine) (p q : 𝔻)
    (hp : L.OrthogonalAt N p) (hq : M.OrthogonalAt N q) : L.lineDist M=discPathDist p q := by
  rw [L.lineDist_eq_halfPlane,discPathDist_eq_halfPlane]
  exact L.toHalfPlane.lineDist_eq_commonOrthogonal M.toHalfPlane N.toHalfPlane _ _
    ((L.orthogonalAt_iff_halfPlane N p).mp hp) ((M.orthogonalAt_iff_halfPlane N q).mp hq)

theorem DiscLine.exists_commonOrthogonal_minimum (L M : DiscLine) (hd : L.HDisjoint M) :
    ∃ (N : DiscLine) (p q : 𝔻), L.OrthogonalAt N p ∧ M.OrthogonalAt N q ∧
      L.lineDist M=discPathDist p q ∧
      ∀ z ∈ L.carrier, ∀ w ∈ M.carrier, discPathDist p q≤discPathDist z w := by
  obtain ⟨N,⟨hL,hM⟩,_⟩ := L.existsUnique_commonOrthogonal M hd
  obtain ⟨p,hp⟩ := (L.orthogonal_iff_exists_orthogonalAt N).mp hL
  obtain ⟨q,hq⟩ := (M.orthogonal_iff_exists_orthogonalAt N).mp hM
  refine ⟨N,p,q,hp,hq,L.lineDist_eq_commonOrthogonal M N p q hp hq,?_⟩
  intro z hz w hw
  rw [← L.lineDist_eq_commonOrthogonal M N p q hp hq]
  exact L.lineDist_le_dist M hz hw


theorem HalfPlaneLine.lineDist_comm (L M : HalfPlaneLine) : L.lineDist M=M.lineDist L := by
  have he : L.pairDistances M=M.pairDistances L := by
    ext d
    constructor <;> rintro ⟨z,hz,w,hw,rfl⟩ <;> exact ⟨w,hw,z,hz,dist_comm _ _⟩
  rw [HalfPlaneLine.lineDist,HalfPlaneLine.lineDist,he]

theorem HalfPlaneLine.lineDist_isometry_image (L M L' M' : HalfPlaneLine)
    (f : ℍ → ℍ) (hf : Isometry f)
    (hL : f '' L.carrier=L'.carrier) (hM : f '' M.carrier=M'.carrier) :
    L'.lineDist M'=L.lineDist M := by
  have he : L'.pairDistances M'=L.pairDistances M := by
    ext d
    constructor
    · rintro ⟨z,hz,w,hw,rfl⟩
      rw [← hL] at hz
      rw [← hM] at hw
      obtain ⟨a,ha,rfl⟩ := hz
      obtain ⟨b,hb,rfl⟩ := hw
      exact ⟨a,ha,b,hb,hf.dist_eq a b⟩
    · rintro ⟨a,ha,b,hb,rfl⟩
      exact ⟨f a,hL ▸ mem_image_of_mem f ha,f b,hM ▸ mem_image_of_mem f hb,(hf.dist_eq a b).symm⟩
  rw [HalfPlaneLine.lineDist,HalfPlaneLine.lineDist,he]

theorem HalfPlaneLine.lineDist_pos (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    0<L.lineDist M := by
  obtain ⟨N,p,q,hp,hq,he,_⟩ := L.exists_commonOrthogonal_minimum M hd
  rw [he]
  apply dist_pos.mpr
  intro hpq
  exact Set.disjoint_left.mp hd.2.2 hp.1 (hpq ▸ hq.1)

theorem concentric_lineDist (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    (HalfPlaneLine.circle 0 s hs).lineDist (HalfPlaneLine.circle 0 t ht)=|Real.log (s/t)| := by
  let p : ℍ := UpperHalfPlane.mk ⟨0,s⟩ hs
  let q : ℍ := UpperHalfPlane.mk ⟨0,t⟩ ht
  have hp : p ∈ (HalfPlaneLine.circle 0 s hs).carrier := by
    apply norm_sub_real_eq_of_sq hs
    change (0-0)^2+s^2=s^2
    ring
  have hq : q ∈ (HalfPlaneLine.circle 0 t ht).carrier := by
    apply norm_sub_real_eq_of_sq ht
    change (0-0)^2+t^2=t^2
    ring
  have hp' : (HalfPlaneLine.circle 0 s hs).OrthogonalAt (HalfPlaneLine.vertical 0) p :=
    ((HalfPlaneLine.circle 0 s hs).orthogonalAt_iff_coefficients (HalfPlaneLine.vertical 0) p hp (show p.re=0 from
      rfl)).mpr rfl
  have hq' : (HalfPlaneLine.circle 0 t ht).OrthogonalAt (HalfPlaneLine.vertical 0) q :=
    ((HalfPlaneLine.circle 0 t ht).orthogonalAt_iff_coefficients (HalfPlaneLine.vertical 0) q hq (show q.re=0 from
      rfl)).mpr rfl
  rw [HalfPlaneLine.lineDist_eq_commonOrthogonal _ _ _ p q hp' hq',metric_vertical_distance (show p.re=q.re from rfl)]
  rfl

theorem DiscLine.lineDist_comm (L M : DiscLine) : L.lineDist M=M.lineDist L := by
  rw [L.lineDist_eq_halfPlane,M.lineDist_eq_halfPlane,L.toHalfPlane.lineDist_comm M.toHalfPlane]

theorem DiscLine.lineDist_pos (L M : DiscLine) (hd : L.HDisjoint M) : 0<L.lineDist M := by
  rw [L.lineDist_eq_halfPlane]
  exact L.toHalfPlane.lineDist_pos M.toHalfPlane ((L.hDisjoint_iff_halfPlane M).mp hd)

end
end LowDimensionalTopology.Geometry.Hyperbolic
