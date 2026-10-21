/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Euclidean.Crystallographic.CrystallographicGroups
public import LowDimensionalTopology.Geometry.Euclidean.Crystallographic.AffineLatticeDiscreteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
noncomputable section
open Set Module
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem mobius_affine_parameters_inv (f : Mobius.mobiusInftyStabilizer) :
    Mobius.mobiusMultiplier f⁻¹=(Mobius.mobiusMultiplier f)⁻¹ ∧
      Mobius.mobiusAffineConstant f⁻¹= -((Mobius.mobiusMultiplier f:ℂ)⁻¹*Mobius.mobiusAffineConstant f) := by
  have hi : Mobius.mobiusMultiplier f⁻¹=(Mobius.mobiusMultiplier f)⁻¹ := Mobius.mobiusMultiplierHom.map_inv f
  refine ⟨hi,?_⟩
  have h := (Mobius.mobius_affine_parameters_mul f⁻¹ f).2
  rw [inv_mul_cancel,Mobius.mobius_affine_parameters_one.2,hi,Units.val_inv_eq_inv_val] at h
  linear_combination -h

/-- The true affine transformations with prescribed lattice constants and multiplier subgroup. -/
def affineLatticeStabilizerSubgroup (S : Subgroup ℂˣ) (L : AddSubgroup ℂ)
    (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) : Subgroup Mobius.mobiusInftyStabilizer where
  carrier := {f | Mobius.mobiusMultiplier f∈S ∧ Mobius.mobiusAffineConstant f∈L}
  one_mem' := by
    change Mobius.mobiusMultiplier 1∈S ∧ Mobius.mobiusAffineConstant 1∈L
    rw [Mobius.mobius_affine_parameters_one.1,Mobius.mobius_affine_parameters_one.2];exact ⟨S.one_mem,L.zero_mem⟩
  mul_mem' {f g} hf hg := by
    change Mobius.mobiusMultiplier f∈S ∧ Mobius.mobiusAffineConstant f∈L at hf
    change Mobius.mobiusMultiplier g∈S ∧ Mobius.mobiusAffineConstant g∈L at hg
    change Mobius.mobiusMultiplier (f*g)∈S ∧ Mobius.mobiusAffineConstant (f*g)∈L
    rw [(Mobius.mobius_affine_parameters_mul f g).1,(Mobius.mobius_affine_parameters_mul f g).2]
    exact ⟨S.mul_mem hf.1 hg.1,L.add_mem (hSL _ hf.1 _ hg.2) hf.2⟩
  inv_mem' {f} hf := by
    change Mobius.mobiusMultiplier f∈S ∧ Mobius.mobiusAffineConstant f∈L at hf
    change Mobius.mobiusMultiplier f⁻¹∈S ∧ Mobius.mobiusAffineConstant f⁻¹∈L
    rw [(mobius_affine_parameters_inv f).1,(mobius_affine_parameters_inv f).2]
    refine ⟨S.inv_mem hf.1,L.neg_mem ?_⟩
    simpa only [Units.val_inv_eq_inv_val] using hSL _ (S.inv_mem hf.1) _ hf.2

/-- The lattice-affine subgroup lies in the actual Mobius group. -/
def affineLatticeGroup (S : Subgroup ℂˣ) (L : AddSubgroup ℂ)
    (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) : Subgroup Mobius.complexMobiusGroup :=
  (affineLatticeStabilizerSubgroup S L hSL).map Mobius.mobiusInftyStabilizer.subtype

theorem affineLatticeGroup_le_inftyStabilizer (S : Subgroup ℂˣ) (L : AddSubgroup ℂ)
    (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) : affineLatticeGroup S L hSL ≤ Mobius.mobiusInftyStabilizer := by
  rintro _ ⟨f,_,rfl⟩
  exact f.property

theorem affineLatticeGroup_mem_iff (S : Subgroup ℂˣ) (L : AddSubgroup ℂ)
    (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) (f : Mobius.complexMobiusGroup) :
    f∈affineLatticeGroup S L hSL ↔ ∃ a∈S,∃ b∈L,f=Mobius.affineMobius a b (Units.ne_zero a) := by
  constructor
  · rintro ⟨g,hg,rfl⟩
    change Mobius.mobiusMultiplier g∈S ∧ Mobius.mobiusAffineConstant g∈L at hg
    refine ⟨Mobius.mobiusMultiplier g,hg.1,Mobius.mobiusAffineConstant g,hg.2,?_⟩
    exact Mobius.mobius_affine_representation g
  · rintro ⟨a,ha,b,hb,rfl⟩
    let f : Mobius.mobiusInftyStabilizer := ⟨Mobius.affineMobius a b (Units.ne_zero a),affineMobius_apply_infty a
      b (Units.ne_zero a)⟩
    have hp := Mobius.mobius_affine_parameters_unique f (fun z => affineMobius_apply_coe a b (Units.ne_zero a) z)
    refine ⟨f,?_,rfl⟩
    exact ⟨hp.1.symm ▸ ha,hp.2.symm ▸ hb⟩

theorem affineLatticeGroup_isElementary (S : Subgroup ℂˣ) (L : AddSubgroup ℂ)
    (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) : IsElementary (affineLatticeGroup S L hSL) := by
  apply isElementary_of_boundary_fixed (affineLatticeGroup S L hSL) ∞
  intro f
  exact affineLatticeGroup_le_inftyStabilizer S L hSL f.property

theorem affineLatticeGroup_parameters (S : Subgroup ℂˣ) (L : AddSubgroup ℂ)
    (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) (f : affineLatticeGroup S L hSL) :
    Mobius.mobiusMultiplier ⟨f.val,affineLatticeGroup_le_inftyStabilizer S L hSL f.property⟩∈S ∧
      Mobius.mobiusAffineConstant ⟨f.val,affineLatticeGroup_le_inftyStabilizer S L hSL f.property⟩∈L := by
  obtain ⟨g,hg,hgf⟩ := f.property
  change g.val=f.val at hgf
  have he : (⟨f.val,affineLatticeGroup_le_inftyStabilizer S L hSL f.property⟩:Mobius.mobiusInftyStabilizer)=g :=
    Subtype.ext hgf.symm
  rw [he]
  exact hg

theorem affineLatticeGroup_multiplierRange (S : Subgroup ℂˣ) (L : AddSubgroup ℂ)
    (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) :
    Mobius.subgroupMultiplierRange (affineLatticeGroup S L hSL)
      (affineLatticeGroup_le_inftyStabilizer S L hSL)=S := by
  ext a
  constructor
  · rintro ⟨f,hf⟩
    rw [← hf]
    exact (affineLatticeGroup_parameters S L hSL f).1
  · intro ha
    have hf : Mobius.affineMobius a 0 (Units.ne_zero a)∈affineLatticeGroup S L hSL :=
      (affineLatticeGroup_mem_iff S L hSL _).mpr ⟨a,ha,0,L.zero_mem,rfl⟩
    let f : affineLatticeGroup S L hSL := ⟨Mobius.affineMobius a 0 (Units.ne_zero a),hf⟩
    refine ⟨f,?_⟩
    exact (Mobius.mobius_affine_parameters_unique
      ⟨f.val,affineLatticeGroup_le_inftyStabilizer S L hSL f.property⟩
        (fun z => affineMobius_apply_coe a 0 (Units.ne_zero a) z)).1

theorem affineLatticeGroup_translationDisplacements (S : Subgroup ℂˣ) (L : AddSubgroup ℂ)
    (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) : translationDisplacements (affineLatticeGroup S L hSL)=L := by
  ext b
  change mobiusTranslation b∈affineLatticeGroup S L hSL ↔ b∈L
  constructor
  · intro hb
    let f : affineLatticeGroup S L hSL := ⟨mobiusTranslation b,hb⟩
    have hm := (affineLatticeGroup_parameters S L hSL f).2
    have hp := (Mobius.mobius_affine_parameters_unique (a := 1) (b := b)
      ⟨f.val,affineLatticeGroup_le_inftyStabilizer S L hSL f.property⟩
        (fun z => by
          change (mobiusTranslation b).val z=(((1:ℂ)*z+b:ℂ):Mobius.ExtendedComplex)
          simpa only [one_mul] using mobiusTranslation_coe b z)).2
    exact hp ▸ hm
  · intro hb
    exact (affineLatticeGroup_mem_iff S L hSL _).mpr ⟨1,S.one_mem,b,hb,rfl⟩

theorem affineLatticeGroup_discrete (S : Subgroup ℂˣ) [Finite S] (L : AddSubgroup ℂ)
    [DiscreteTopology L] (hSL : ∀ a∈S,∀ b∈L,(a:ℂ)*b∈L) :
    Mobius.IsDiscreteMobiusSubgroup (affineLatticeGroup S L hSL) := by
  apply affineLattice_discrete _ (affineLatticeGroup_le_inftyStabilizer S L hSL) L
  · rw [affineLatticeGroup_multiplierRange]
    exact Set.toFinite _
  · intro f
    exact (affineLatticeGroup_parameters S L hSL f).2


/-- The actual two-generator integer lattice associated with a nonreal complex number. -/
def quadraticComplexLattice (a : ℂ) : AddSubgroup ℂ :=
  (Submodule.span ℤ (Set.range ![1,a])).toAddSubgroup

theorem one_nonreal_linearIndependent (a : ℂ) (ha : a.im≠0) :
    LinearIndependent ℝ ![1,a] := by
  apply linearIndependent_fin2.mpr
  change a≠0 ∧ ∀ r : ℝ,r • a≠(1:ℂ)
  refine ⟨fun h => ha (by rw [h];rfl),?_⟩
  intro r h
  have hi := congrArg Complex.im h
  simp only [Complex.real_smul,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,Complex.one_im] at hi
  have hr : r=0 := (mul_eq_zero.mp hi).resolve_right ha
  subst r
  norm_num only [zero_smul] at h

theorem quadraticComplexLattice_discrete (a : ℂ) (ha : a.im≠0) :
    DiscreteTopology (quadraticComplexLattice a) := by
  let b : Basis (Fin 2) ℝ ℂ := basisOfLinearIndependentOfCardEqFinrank
    (one_nonreal_linearIndependent a ha) (by simp [Complex.finrank_real_complex])
  have he : (b:Fin 2→ℂ)=![1,a] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  change DiscreteTopology (Submodule.span ℤ (Set.range ![1,a]))
  have hL : Submodule.span ℤ (Set.range b)=Submodule.span ℤ (Set.range ![1,a]) :=
    congrArg (fun f : Fin 2→ℂ => Submodule.span ℤ (Set.range f)) he
  exact hL ▸ (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range b)))

theorem one_mem_quadraticComplexLattice (a : ℂ) : 1∈quadraticComplexLattice a := by
  exact Submodule.subset_span ⟨(0:Fin 2),rfl⟩

theorem self_mem_quadraticComplexLattice (a : ℂ) : a∈quadraticComplexLattice a := by
  exact Submodule.subset_span ⟨(1:Fin 2),rfl⟩

theorem quadraticComplexLattice_mul_mem (a : ℂ) (t : ℤ) (ha : a^2=(t:ℂ)*a-1)
    (z : ℂ) (hz : z∈quadraticComplexLattice a) : a*z∈quadraticComplexLattice a := by
  let L := Submodule.span ℤ (Set.range ![1,a])
  have hle : L≤L.comap (LinearMap.mul ℤ ℂ a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change a*(![1,a] i)∈L
    fin_cases i
    · change a*1∈L
      rw [mul_one]
      exact self_mem_quadraticComplexLattice a
    · change a*a∈L
      rw [← pow_two,ha]
      have hm := L.sub_mem (L.smul_mem t (self_mem_quadraticComplexLattice a)) (one_mem_quadraticComplexLattice a)
      simpa only [zsmul_eq_mul] using hm
  exact hle hz

theorem finite_zpowers_preserves_lattice (a : ℂˣ) (ha : IsOfFinOrder a) (L : AddSubgroup ℂ)
    (hL : ∀ z∈L,(a:ℂ)*z∈L) : ∀ c∈Subgroup.zpowers a,∀ z∈L,(c:ℂ)*z∈L := by
  intro c hc z hz
  have hpow : ∀ n : ℕ,((a^n:ℂˣ):ℂ)*z∈L := by
    intro n
    induction n with
    | zero => simpa only [pow_zero,Units.val_one,one_mul] using hz
    | succ n ih =>
      rw [pow_succ',Units.val_mul,mul_assoc]
      exact hL _ ih
  obtain ⟨n,hn⟩ := ha.mem_powers_iff_mem_zpowers.mpr hc
  change a^n=c at hn
  rw [← hn]
  exact hpow n

theorem quadraticRotation_discriminant_pos (t : ℤ) (ht : -2<t ∧ t<2) :
    0<4-(t:ℝ)^2 := by
  rcases ht with ⟨hlo,hhi⟩
  interval_cases t <;> norm_num

/-- The upper unit-circle root with the prescribed integral real trace. -/
def quadraticRotationRoot (t : ℤ) (ht : -2<t ∧ t<2) : ℂˣ :=
  Units.mk0 ⟨(t:ℝ)/2,Real.sqrt (4-(t:ℝ)^2)/2⟩ (by
    intro h
    have hi := congrArg Complex.im h
    change Real.sqrt (4-(t:ℝ)^2)/2=0 at hi
    have hp := Real.sqrt_pos.mpr (quadraticRotation_discriminant_pos t ht)
    linarith)

theorem quadraticRotationRoot_im_pos (t : ℤ) (ht : -2<t ∧ t<2) :
    0<((quadraticRotationRoot t ht:ℂˣ):ℂ).im := by
  change 0<Real.sqrt (4-(t:ℝ)^2)/2
  positivity [quadraticRotation_discriminant_pos t ht]

theorem quadraticRotationRoot_polynomial (t : ℤ) (ht : -2<t ∧ t<2) :
    ((quadraticRotationRoot t ht:ℂˣ):ℂ)^2=
      (t:ℂ)*((quadraticRotationRoot t ht:ℂˣ):ℂ)-1 := by
  have hs := Real.sq_sqrt (quadraticRotation_discriminant_pos t ht).le
  rw [pow_two]
  apply Complex.ext <;>
    simp only [quadraticRotationRoot,Units.val_mk0,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,Complex.intCast_re,Complex.intCast_im,Complex.one_re,Complex.one_im]
  · nlinarith
  · ring

theorem quadraticRotationRoot_norm (t : ℤ) (ht : -2<t ∧ t<2) :
    ‖((quadraticRotationRoot t ht:ℂˣ):ℂ)‖=1 := by
  have hs := Real.sq_sqrt (quadraticRotation_discriminant_pos t ht).le
  have hsq := Complex.sq_norm ((quadraticRotationRoot t ht:ℂˣ):ℂ)
  simp only [Complex.normSq_apply,quadraticRotationRoot,Units.val_mk0] at hsq
  change ‖(⟨(t:ℝ)/2,Real.sqrt (4-(t:ℝ)^2)/2⟩:ℂ)‖=1
  nlinarith [norm_nonneg (⟨(t:ℝ)/2,Real.sqrt (4-(t:ℝ)^2)/2⟩:ℂ)]

theorem quadraticRotationRoot_ne_one (t : ℤ) (ht : -2<t ∧ t<2) :
    quadraticRotationRoot t ht≠1 := by
  intro h
  have hp := quadraticRotationRoot_im_pos t ht
  rw [h,Units.val_one,Complex.one_im] at hp
  exact lt_irrefl 0 hp

theorem quadraticRotationRoot_sq_ne_one (t : ℤ) (ht : -2<t ∧ t<2) :
    (quadraticRotationRoot t ht)^2≠1 := by
  intro h
  have he := congrArg (fun a : ℂˣ => (a:ℂ)) h
  change ((quadraticRotationRoot t ht:ℂˣ):ℂ)^2=1 at he
  have hp := quadraticRotationRoot_im_pos t ht
  rcases sq_eq_one_iff.mp he with he | he
  · rw [he,Complex.one_im] at hp
    exact lt_irrefl 0 hp
  · rw [he] at hp
    norm_num at hp

theorem quadraticRotationRoot_order_three :
    orderOf (quadraticRotationRoot (-1) (by norm_num))=3 := by
  apply orderOf_eq_prime
  · apply Units.ext
    change ((quadraticRotationRoot (-1) (by norm_num):ℂˣ):ℂ)^3=1
    have hp := quadraticRotationRoot_polynomial (-1) (by norm_num)
    norm_num at hp
    linear_combination (((quadraticRotationRoot (-1) (by norm_num):ℂˣ):ℂ)-1)*hp
  · exact quadraticRotationRoot_ne_one _ _

theorem quadraticRotationRoot_order_four :
    orderOf (quadraticRotationRoot 0 (by norm_num))=4 := by
  have hpow : (quadraticRotationRoot 0 (by norm_num))^4=1 := by
    apply Units.ext
    change ((quadraticRotationRoot 0 (by norm_num):ℂˣ):ℂ)^4=1
    have hp := quadraticRotationRoot_polynomial 0 (by norm_num)
    norm_num at hp
    linear_combination (((quadraticRotationRoot 0 (by norm_num):ℂˣ):ℂ)^2-1)*hp
  have hd := orderOf_dvd_of_pow_eq_one hpow
  have hb := Nat.le_of_dvd (by decide) hd
  have hn := quadraticRotationRoot_sq_ne_one 0 (by norm_num)
  have hn1 := quadraticRotationRoot_ne_one 0 (by norm_num)
  interval_cases h : orderOf (quadraticRotationRoot 0 (by norm_num)) <;>
    simp_all [orderOf_eq_one_iff]
  exact hn (by simpa only [h] using pow_orderOf_eq_one (quadraticRotationRoot 0 (by norm_num)))

theorem quadraticRotationRoot_order_six :
    orderOf (quadraticRotationRoot 1 (by norm_num))=6 := by
  let a := quadraticRotationRoot 1 (by norm_num)
  have hp := quadraticRotationRoot_polynomial 1 (by norm_num)
  have hcube : (a:ℂ)^3= -1 := by
    norm_num only [Int.cast_one,one_mul] at hp
    change (a:ℂ)^2=(a:ℂ)-1 at hp
    linear_combination ((a:ℂ)+1)*hp
  have hpow : a^6=1 := by
    apply Units.ext
    change (a:ℂ)^6=1
    linear_combination ((a:ℂ)^3-1)*hcube
  have hd := orderOf_dvd_of_pow_eq_one hpow
  have hb := Nat.le_of_dvd (by decide) hd
  have hn2 := quadraticRotationRoot_sq_ne_one 1 (by norm_num)
  have hn1 := quadraticRotationRoot_ne_one 1 (by norm_num)
  change a≠1 at hn1
  change a^2≠1 at hn2
  change orderOf a=6
  have hal : orderOf a=1 ∨ orderOf a=2 ∨ orderOf a=3 ∨ orderOf a=6 := by
    interval_cases orderOf a
    all_goals norm_num at hd
    all_goals tauto
  rcases hal with h | h | h | h
  · exact False.elim (hn1 (orderOf_eq_one_iff.mp h))
  · have he : a^2=1 := by simpa only [h] using pow_orderOf_eq_one a
    exact False.elim (hn2 he)
  · have he := congrArg (fun b : ℂˣ => (b:ℂ)) (pow_orderOf_eq_one a)
    rw [h] at he
    change (a:ℂ)^3=1 at he
    rw [hcube] at he
    norm_num at he
  · exact h


/-- Realizability uses an actual discrete elementary Mobius group containing a parabolic element. -/
def HasCrystallographicMultiplierOrder (q : ℕ) : Prop :=
  ∃ H : Subgroup Mobius.complexMobiusGroup,Mobius.IsDiscreteMobiusSubgroup H ∧ IsElementary H ∧
    (∃ p∈H,Mobius.MobiusParabolic p) ∧ ∃ hi : H≤Mobius.mobiusInftyStabilizer,
      Nat.card (Mobius.subgroupMultiplierRange H hi)=q

theorem crystallographic_multiplier_order_of_lattice (a : ℂˣ) (q : ℕ) (horder : orderOf a=q)
    (ha : IsOfFinOrder a) (L : AddSubgroup ℂ) [DiscreteTopology L] (h1 : (1:ℂ)∈L)
    (hL : ∀ z∈L,(a:ℂ)*z∈L) : HasCrystallographicMultiplierOrder q := by
  let S := Subgroup.zpowers a
  have : Finite S := ha.finite_zpowers
  let hSL := finite_zpowers_preserves_lattice a ha L hL
  let H := affineLatticeGroup S L hSL
  let hi := affineLatticeGroup_le_inftyStabilizer S L hSL
  refine ⟨H,affineLatticeGroup_discrete S L hSL,affineLatticeGroup_isElementary S L hSL,
    ⟨mobiusTranslation 1,?_,(mobiusTranslation_parabolic_iff 1).mpr one_ne_zero⟩,hi,?_⟩
  · exact (affineLatticeGroup_mem_iff S L hSL _).mpr ⟨1,S.one_mem,1,h1,rfl⟩
  · rw [affineLatticeGroup_multiplierRange]
    exact (Nat.card_zpowers a).trans horder

theorem crystallographic_quadratic_order_realizable (t : ℤ) (ht : -2<t ∧ t<2)
    (q : ℕ) (hq : 0<q) (horder : orderOf (quadraticRotationRoot t ht)=q) :
    HasCrystallographicMultiplierOrder q := by
  let a := quadraticRotationRoot t ht
  let L := quadraticComplexLattice (a:ℂ)
  have hfinite : IsOfFinOrder a := orderOf_pos_iff.mp (by rw [horder];exact hq)
  have : DiscreteTopology L := quadraticComplexLattice_discrete _ (quadraticRotationRoot_im_pos t ht).ne'
  apply crystallographic_multiplier_order_of_lattice a q horder hfinite L (one_mem_quadraticComplexLattice _)
  exact quadraticComplexLattice_mul_mem (a:ℂ) t (quadraticRotationRoot_polynomial t ht)

theorem crystallographic_order_one_realizable : HasCrystallographicMultiplierOrder 1 := by
  let L := quadraticComplexLattice Complex.I
  have : DiscreteTopology L := quadraticComplexLattice_discrete _ (by norm_num)
  apply crystallographic_multiplier_order_of_lattice 1 1 (by simp)
    (orderOf_pos_iff.mp (by simp)) L (one_mem_quadraticComplexLattice _)
  intro z hz
  simpa only [Units.val_one,one_mul] using hz

theorem crystallographic_order_two_realizable : HasCrystallographicMultiplierOrder 2 := by
  let L := quadraticComplexLattice Complex.I
  have : DiscreteTopology L := quadraticComplexLattice_discrete _ (by norm_num)
  have ho : orderOf (-1:ℂˣ)=2 := by rw [← orderOf_units];norm_num
  apply crystallographic_multiplier_order_of_lattice (-1) 2 ho
    (orderOf_pos_iff.mp (by rw [ho];norm_num)) L (one_mem_quadraticComplexLattice _)
  intro z hz
  change (-1:ℂ)*z∈L
  rw [neg_one_mul]
  exact L.neg_mem hz

theorem crystallographic_orders_realizable (q : ℕ) (hq : q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=6) :
    HasCrystallographicMultiplierOrder q := by
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact crystallographic_order_one_realizable
  · exact crystallographic_order_two_realizable
  · exact crystallographic_quadratic_order_realizable (-1) (by norm_num) 3 (by norm_num)
      quadraticRotationRoot_order_three
  · exact crystallographic_quadratic_order_realizable 0 (by norm_num) 4 (by norm_num)
      quadraticRotationRoot_order_four
  · exact crystallographic_quadratic_order_realizable 1 (by norm_num) 6 (by norm_num)
      quadraticRotationRoot_order_six

end LowDimensionalTopology.Geometry.DiscreteGroups
