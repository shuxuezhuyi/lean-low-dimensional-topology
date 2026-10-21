module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.FinitelyGeneratedCyclicClasses
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TwoMirrorRotations
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianElementary
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.AlternativeElementarity
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A reflection inverting a genuine rotation has the exact even-power
conjugation formula, in an arbitrary original group. -/
theorem inversion_reflection_conjugation_zpow
    {G : Type*} [Group G] (r a : G) (ha : a*a=1)
    (har : a*r*a = r⁻¹) (n : ℤ) :
    r^n*a*(r^n)⁻¹ = r^(2*n)*a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hconj : a*r*a⁻¹ = r⁻¹ := by rw [hai]; exact har
  have hswap (m : ℤ) : a*r^m = r^(-m)*a := by
    have hp : a*r^m*a⁻¹ = r^(-m) := by
      rw [←conj_zpow,hconj]
      simp only [inv_zpow,zpow_neg]
    have hh := congrArg (fun x : G => x*a) hp
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  rw [←zpow_neg,mul_assoc,hswap (-n),neg_neg,←mul_assoc,←zpow_add]
  rw [show n+n = 2*n by omega]

/-- Every reflected word in two genuine involutions is conjugate in their
actual generated subgroup to one of the two original involutions. The
conjugating word is an actual power of their product. -/
theorem two_involutions_reflection_two_conjugates
    {G : Type*} [Group G] (a b : G) (ha : a*a=1) (hb : b*b=1) (n : ℤ) :
    (∃ m : ℤ, (a*b)^m*a*((a*b)^m)⁻¹ = (a*b)^n*a) ∨
      (∃ m : ℤ, (a*b)^m*b*((a*b)^m)⁻¹ = (a*b)^n*a) := by
  let r := a*b
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have har : a*r*a = r⁻¹ := by
    dsimp [r]
    rw [mul_inv_rev,hai,hbi,←mul_assoc,ha,one_mul]
  have hbr : b*r*b = r⁻¹ := by
    dsimp [r]
    rw [mul_inv_rev,hai,hbi,mul_assoc,mul_assoc,hb,mul_one]
  let m := n/2
  have hpar : n = 2*m ∨ n = 2*m+1 := by dsimp [m]; omega
  rcases hpar with hn | hn
  · exact Or.inl ⟨m,(inversion_reflection_conjugation_zpow r a ha har m).trans
      (by rw [hn])⟩
  · refine Or.inr ⟨m+1,(inversion_reflection_conjugation_zpow r b hb hbr (m+1)).trans ?_⟩
    have hbRel : b = r⁻¹*a := by
      dsimp [r]
      rw [mul_inv_rev,hai,hbi,mul_assoc,ha,mul_one]
    change r^(2*(m+1))*b = r^n*a
    rw [hbRel,←mul_assoc,←zpow_neg_one,←zpow_add]
    rw [show 2*(m+1)+(-1:ℤ) = n by omega]

/-- A genuinely cyclic original group has at most one actual maximal cyclic
subgroup of either geometric type, hence at most one genuine class. -/
theorem cyclic_cyclic_classes_subsingleton
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hc : IsCyclic
      H)
    (kind : FuchsianCyclicKind) : Subsingleton (FuchsianCyclicConjugacyClasses D kind) := by
  have he (K : fuchsianMaximalCyclicSubgroups H kind) : K.val = H :=
    (K.property.1.2.2 H le_rfl hc K.property.1.1).symm
  let : Subsingleton (fuchsianMaximalCyclicSubgroups H kind) :=
    ⟨fun K L => Subtype.ext ((he K).trans (he L).symm)⟩
  change Subsingleton (Quotient _)
  exact inferInstance

/-- Actual cyclic groups have finite actual maximal cyclic class spaces. -/
theorem cyclic_cyclic_classes_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hc : IsCyclic
      H)
    (kind : FuchsianCyclicKind) : Finite (FuchsianCyclicConjugacyClasses D kind) := by
  let := cyclic_cyclic_classes_subsingleton D hc kind
  exact Finite.of_subsingleton

/-- A finite set of actual element conjugacy representatives gives a finite
actual geometric maximal cyclic subgroup class space. No model class labels
or assumed finite maximal subgroup family are substituted. -/
theorem cyclic_classes_finite_of_finite_element_representatives
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (kind :
      FuchsianCyclicKind)
    (S : Set H) (hS : S.Finite)
    (hrep : ∀ f : H, MobiusCyclicType kind f.val → ∃ s ∈ S, IsConj f s) :
    Finite (FuchsianCyclicConjugacyClasses D kind) := by
  classical
  let C := FuchsianCyclicConjugacyClasses D kind
  have hex (c : C) : ∃ s : S, ∃ f : H,
      f.val ∈ (chosenFuchsianMaximalCyclic D kind c).val ∧ f ≠ 1 ∧ IsConj f s.val := by
    obtain ⟨f,hfK,hft⟩ := (chosenFuchsianMaximalCyclic D kind c).property.2
    let F : H := ⟨f,(chosenFuchsianMaximalCyclic D kind c).property.1.1 hfK⟩
    have hFn : F ≠ 1 := by
      cases kind <;> exact fun he => hft.1 (congrArg Subtype.val he)
    obtain ⟨s,hs,hFs⟩ := hrep F hft
    exact ⟨⟨s,hs⟩,F,hfK,hFn,hFs⟩
  choose s f hfK hfn hfs using hex
  have hsInjective : Function.Injective s := by
    intro c d he
    have hcd : IsConj (f c) (f d) := by
      have hh := hfs c
      rw [he] at hh
      exact hh.trans (hfs d).symm
    have hh := maximal_cyclic_classes_eq_of_nonidentity_isConj D kind
      (chosenFuchsianMaximalCyclic D kind c) (chosenFuchsianMaximalCyclic D kind d)
      (f c) (f d) (hfK c) (hfK d) (hfn c) (hfn d) hcd
    simpa only [chosenFuchsianMaximalCyclic,Quotient.out_eq] using hh
  let : Finite S := hS.to_subtype
  exact Finite.of_injective s hsInjective

/-- A finite-order word in an actual infinite dihedral group is the identity
or is conjugate, by an actual rotation word, to one of its two involutions. -/
theorem two_involutions_finiteOrder_conjugate
    {G : Type*} [Group G] (a b : G) (ha : a*a=1) (hb : b*b=1)
    (hinj : Function.Injective (fun n : ℤ => (a*b)^n))
    (f : G) (hf : f ∈ Subgroup.closure ({a,b}:Set G)) (hfin : IsOfFinOrder f) :
    f=1 ∨ (∃ m : ℤ, (a*b)^m*a*((a*b)^m)⁻¹=f) ∨
      ∃ m : ℤ, (a*b)^m*b*((a*b)^m)⁻¹=f := by
  obtain ⟨n,rfl|rfl⟩ := two_involutions_zpow_normal_form a b ha hb f hf
  · left
    obtain ⟨k,hk,he⟩ := hfin.exists_pow_eq_one
    have hz : n*(k:ℤ)=0 := hinj (by
      change (a*b)^(n*(k:ℤ))=(a*b)^(0:ℤ)
      rw [zpow_mul,zpow_natCast,zpow_zero]
      exact he)
    have hn : n=0 := (mul_eq_zero.mp hz).resolve_right (by exact_mod_cast hk.ne')
    rw [hn,zpow_zero]
  · exact Or.inr (two_involutions_reflection_two_conjugates a b ha hb n)

/-- Every actual finite-order element of an infinite dihedral group has square
one; this includes all actual discrete elliptics. -/
theorem two_involutions_finiteOrder_square
    {G : Type*} [Group G] (a b : G) (ha : a*a=1) (hb : b*b=1)
    (hinj : Function.Injective (fun n : ℤ => (a*b)^n))
    (f : G) (hf : f ∈ Subgroup.closure ({a,b}:Set G)) (hfin : IsOfFinOrder f) : f^2=1 := by
  rcases two_involutions_finiteOrder_conjugate a b ha hb hinj f hf hfin with
    rfl | ⟨m,rfl⟩ | ⟨m,rfl⟩
  · simp only [one_pow]
  · rw [conj_pow,pow_two,ha]; simp only [mul_one,mul_inv_cancel]
  · rw [conj_pow,pow_two,hb]; simp only [mul_one,mul_inv_cancel]

/-- A complex scaling with multiplier of modulus different from one has
injective actual two-sided powers. -/
theorem mobiusScaling_zpow_injective (d : ℂˣ) (hd : ‖(d:ℂ)‖≠1) :
    Function.Injective (fun n : ℤ => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n) := by
  intro m n he
  have hm : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (d^m)=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^m := map_zpow _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom d m
  have hn : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (d^n)=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n := map_zpow _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom d n
  have hu := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_parameter_injective (hm.trans (he.trans
    hn.symm))
  have hnorm := congrArg (fun x : ℂˣ => ‖(x:ℂ)‖) hu
  simp only [Units.val_zpow_eq_zpow_val,norm_zpow] at hnorm
  exact zpow_right_injective₀ (norm_pos_iff.mpr d.ne_zero) hd hnorm

/-- The literal Fuchsian half-turn exchanges zero and infinity. -/
theorem fuchsianDihedralFlip_endpoints :
    fuchsianDihedralFlip.val (0:ℂ)=∞ ∧ fuchsianDihedralFlip.val ∞=(0:ℂ) := by
  constructor
  · change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    (-1)).val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val (0:ℂ))=∞
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_zero,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty]
  · change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    (-1)).val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val ∞)=(0:ℂ)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_infty,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero]

/-- A positive dilation and the literal half-turn generate exactly the two
involutions needed for the genuine dihedral word theorem. -/
theorem scaling_flip_two_involutions (d : ℂˣ) :
    let r := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d
    let b := fuchsianDihedralFlip
    let a := r*b
    a*a=1 ∧ b*b=1 ∧ a*b=r ∧
      Subgroup.closure ({r,b}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=Subgroup.closure ({a,b}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  dsimp only
  have hb := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square fuchsianDihedralFlip
    fuchsianDihedralFlip_endpoints.1 fuchsianDihedralFlip_endpoints.2
  have ha := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip)
    (by change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d).val (fuchsianDihedralFlip.val (0:ℂ))=∞
        rw [fuchsianDihedralFlip_endpoints.1,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty])
    (by change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d).val (fuchsianDihedralFlip.val ∞)=(0:ℂ)
        rw [fuchsianDihedralFlip_endpoints.2,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero])
  have hr : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip*fuchsianDihedralFlip=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d := by
    rw [mul_assoc,hb,mul_one]
  refine ⟨ha,hb,hr,le_antisymm ?_ ?_⟩
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | hx
    · have hh : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
      d*fuchsianDihedralFlip)*fuchsianDihedralFlip ∈
          Subgroup.closure
            ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
                d*fuchsianDihedralFlip,fuchsianDihedralFlip}:Set
              _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
          (Subgroup.subset_closure (Or.inr rfl))
      exact Eq.mp (congrArg (fun x : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup =>
        x ∈ Subgroup.closure
          ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
              d*fuchsianDihedralFlip,fuchsianDihedralFlip}:Set
            _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) hr) hh
    · rw [mem_singleton_iff] at hx
      exact hx ▸ Subgroup.subset_closure (Or.inr rfl)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
        (Subgroup.subset_closure (Or.inr rfl))
    · rw [mem_singleton_iff] at hx
      exact hx ▸ Subgroup.subset_closure (Or.inr rfl)

/-- Every genuine discrete elliptic in the literal positive-dilation dihedral
group has square one. The conclusion concerns the original actual map. -/
theorem scaling_flip_elliptic_square
    {K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc K)
    (d : ℂˣ) (hd : ‖(d:ℂ)‖≠1)
    (hK : K=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d,fuchsianDihedralFlip}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈K) (he : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : f^2=1 := by
  obtain ⟨ha,hb,hr,hgen⟩ := scaling_flip_two_involutions d
  have hi : Function.Injective (fun n : ℤ =>
      ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip)*fuchsianDihedralFlip)^n) := by
    rw [hr]
    exact mobiusScaling_zpow_injective d hd
  apply two_involutions_finiteOrder_square (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    d*fuchsianDihedralFlip)
    fuchsianDihedralFlip ha hb hi f
  · rwa [hK,hgen] at hf
  · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elliptic_finiteOrder K D.discrete f hf he

/-- The original elementary Fuchsian group is cyclic, or every actual elliptic
has order dividing two. No finite-side or finite-class hypothesis is added. -/
theorem elementary_fuchsian_cyclic_or_elliptic_square_eq_one
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (he :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) :
    IsCyclic H ∨ ∀ f ∈ H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f → f^2=1 := by
  rcases D.elementary_classification he with hc | ⟨q,d,_hdi,hdb,hK⟩
  · exact Or.inl hc
  · right
    have hd : ‖(d:ℂ)‖≠1 := ne_of_gt (lt_of_lt_of_le hdb (Complex.re_le_norm _))
    intro f hf hfe
    have hqf : q*f*q⁻¹∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H :=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
        _).mpr ⟨f,hf,rfl⟩
    have hqe : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (q*f*q⁻¹) := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f q).mpr hfe
    have hh := scaling_flip_elliptic_square (D.nielsenConjugate q) d hd hK _ hqf hqe
    apply (MulAut.conj q).injective
    change q*f^2*q⁻¹=q*1*q⁻¹
    rw [←conj_pow,hh]
    simp only [mul_one,mul_inv_cancel]

/-- The literal dihedral group has actual rotation or reflected-rotation
normal forms, with the original dilation itself as rotation generator. -/
theorem scaling_flip_normal_form (d : ℂˣ) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f∈Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d,fuchsianDihedralFlip}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) :
    ∃ n : ℤ, f=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n ∨
      f=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip) := by
  obtain ⟨ha,hb,hr,hgen⟩ := scaling_flip_two_involutions d
  rw [hgen] at hf
  obtain ⟨n,hn⟩ := two_involutions_zpow_normal_form
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip) fuchsianDihedralFlip ha hb f hf
  exact ⟨n,by simpa only [hr] using hn⟩

/-- No actual word in the literal dilation and half-turn group is parabolic:
rotation words fix both original endpoints, and reflected words have square one. -/
theorem scaling_flip_not_parabolic (d : ℂˣ) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f∈Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d,fuchsianDihedralFlip}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) :
    ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f := by
  intro hp
  obtain ⟨n,rfl|rfl⟩ := scaling_flip_normal_form d f hf
  · have hm : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (d^n)=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n := map_zpow _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom d n
    obtain ⟨a,ha⟩ := hp.2
    have hz : (((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=a := (ha _).mp (by rw [←hm,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero])
    have hi : (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=a := (ha _).mp (by rw [←hm,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty])
    exact OnePoint.coe_ne_infty (0:ℂ) (hz.trans hi.symm)
  · have hm : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (d^n)=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n := map_zpow _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom d n
    have hs : ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip))^2=1 := by
      have hh := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square
        ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
          d)^n*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip))
        (by change ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n).val ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d).val (fuchsianDihedralFlip.val (0:ℂ)))=∞
            rw [fuchsianDihedralFlip_endpoints.1,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty,←hm,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty])
        (by change ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^n).val ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d).val (fuchsianDihedralFlip.val ∞))=(0:ℂ)
            rw [fuchsianDihedralFlip_endpoints.2,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero,←hm,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero])
      simpa only [pow_two] using hh
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder _ (Or.inl hp)
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hs⟩)

/-- A literal infinite dihedral Fuchsian group has finite actual elliptic and
parabolic maximal cyclic class spaces. The two elliptic representatives are
actual members of the group, and every conjugator is an actual rotation word. -/
theorem scaling_flip_cyclic_classes_finite
    {K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc K)
    (d : ℂˣ) (hd : ‖(d:ℂ)‖≠1)
    (hK : K=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d,fuchsianDihedralFlip}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
    (kind : FuchsianCyclicKind) : Finite (FuchsianCyclicConjugacyClasses D kind) := by
  have hrK : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d∈K := by rw [hK]; exact Subgroup.subset_closure (Or.inl rfl)
  have hbK : fuchsianDihedralFlip∈K := by rw [hK]; exact Subgroup.subset_closure (Or.inr rfl)
  let a : K := ⟨_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip,K.mul_mem hrK hbK⟩
  let b : K := ⟨fuchsianDihedralFlip,hbK⟩
  apply cyclic_classes_finite_of_finite_element_representatives D kind ({a,b}:Set K) (Set.toFinite _)
  intro f hft
  cases kind with
  | parabolic => exact False.elim (scaling_flip_not_parabolic d f.val (hK ▸ f.property) hft)
  | elliptic =>
    obtain ⟨ha,hb,hr,hgen⟩ := scaling_flip_two_involutions d
    have hinj : Function.Injective (fun n : ℤ =>
        ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip)*fuchsianDihedralFlip)^n) := by
      rw [hr]
      exact mobiusScaling_zpow_injective d hd
    have hf : f.val∈Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d*fuchsianDihedralFlip,fuchsianDihedralFlip}:Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
      (hK.trans hgen) ▸ f.property
    have hfin := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elliptic_finiteOrder K D.discrete f.val f.property hft
    rcases two_involutions_finiteOrder_conjugate
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
        d*fuchsianDihedralFlip) fuchsianDihedralFlip ha hb hinj f.val hf hfin with
      hf1 | ⟨m,hm⟩ | ⟨m,hm⟩
    · exact False.elim (hft.1 hf1)
    · let c : K := ⟨(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^m,K.zpow_mem hrK m⟩
      have hconj : IsConj a f := by
        apply isConj_iff.mpr
        refine ⟨c,Subtype.ext ?_⟩
        change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
          d)^m*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
          d*fuchsianDihedralFlip)*((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^m)⁻¹=f.val
        simpa only [hr] using hm
      exact ⟨a,Or.inl rfl,hconj.symm⟩
    · let c : K := ⟨(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^m,K.zpow_mem hrK m⟩
      have hconj : IsConj b f := by
        apply isConj_iff.mpr
        refine ⟨c,Subtype.ext ?_⟩
        change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
          d)^m*fuchsianDihedralFlip*((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d)^m)⁻¹=f.val
        simpa only [hr] using hm
      exact ⟨b,Or.inr rfl,hconj.symm⟩

/-- Every original elementary Fuchsian group has only finitely many actual
maximal elliptic and parabolic cyclic conjugacy classes, without any finite
sidedness, finite-generation, or standard-disc assumption. -/
theorem elementary_cyclic_classes_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (kind : FuchsianCyclicKind) :
    Finite (FuchsianCyclicConjugacyClasses D kind) := by
  rcases D.elementary_classification he with hc | ⟨q,d,_hdi,hdb,hK⟩
  · exact cyclic_cyclic_classes_finite D hc kind
  · have hd : ‖(d:ℂ)‖≠1 := ne_of_gt (lt_of_lt_of_le hdb (Complex.re_le_norm _))
    let := scaling_flip_cyclic_classes_finite (D.nielsenConjugate q) d hd hK kind
    exact Finite.of_equiv _
      (fuchsianCyclicConjugacyClassesConjugationEquiv D q (D.nielsenConjugate q) rfl kind).symm

/-- The full original finite-generation hypothesis supplies finitely many
actual maximal cyclic classes of both geometric types, including elementary
groups. No non-elementarity hypothesis is added. -/
theorem finitelyGenerated_all_cyclic_classes_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hFG : H.FG) (kind : FuchsianCyclicKind) :
    Finite (FuchsianCyclicConjugacyClasses D kind) := by
  by_cases he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H
  · exact elementary_cyclic_classes_finite D he kind
  · exact finitelyGenerated_cyclic_classes_finite D he hFG kind

/--
For the original finitely generated Fuchsian
group, finitely many actual maximal elliptic or parabolic cyclic subgroups
supply the unique nonidentity member conjugate to each original typed map.
-/
theorem cyclic_conjugacyClasses_finite_and_unique_representatives_of_fg
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (hFG : H.FG) (kind : FuchsianCyclicKind) :
    Finite (FuchsianCyclicConjugacyClasses D kind) ∧
      ∀ f : H, MobiusCyclicType kind f.val →
        ∃! r : FuchsianCyclicRepresentativeMembers D kind, IsConj f r.2.val :=
  ⟨finitelyGenerated_all_cyclic_classes_finite D hFG kind,
    fuchsianCyclicRepresentativeMembers_unique_conjugate D kind⟩

end LowDimensionalTopology.Geometry.Fuchsian
