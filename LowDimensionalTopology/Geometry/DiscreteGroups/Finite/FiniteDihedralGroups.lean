/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteCyclicGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DihedralExtensions
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteBranchProfiles

@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem mobiusScaling_mul (a b : ℂˣ) :
    Mobius.mobiusScaling (a*b) = Mobius.mobiusScaling a * Mobius.mobiusScaling b := by
  apply Subtype.ext
  ext z
  cases z using OnePoint.rec with
  | infty =>
    change (Mobius.mobiusScaling (a*b)).val ∞ = (Mobius.mobiusScaling a).val ((Mobius.mobiusScaling b).val ∞)
    rw [Mobius.mobiusScaling_infty,Mobius.mobiusScaling_infty,Mobius.mobiusScaling_infty]
  | coe z =>
    change (Mobius.mobiusScaling (a*b)).val z = (Mobius.mobiusScaling a).val ((Mobius.mobiusScaling b).val z)
    rw [Mobius.mobiusScaling_coe,Mobius.mobiusScaling_coe,Mobius.mobiusScaling_coe]
    simp only [Units.val_mul,mul_assoc]

theorem mobiusScaling_one : Mobius.mobiusScaling 1 = 1 := by
  apply Subtype.ext
  ext z
  cases z using OnePoint.rec with
  | infty => exact Mobius.mobiusScaling_infty 1
  | coe z =>
    change (Mobius.mobiusScaling 1).val z = (z : Mobius.ExtendedComplex)
    simpa only [Units.val_one,one_mul] using Mobius.mobiusScaling_coe 1 z

theorem mobiusScaling_inv (a : ℂˣ) : (Mobius.mobiusScaling a)⁻¹ = Mobius.mobiusScaling a⁻¹ := by
  apply inv_eq_of_mul_eq_one_left
  rw [← mobiusScaling_mul,inv_mul_cancel,mobiusScaling_one]

theorem mobiusReciprocal_mul_scaling (a : ℂˣ) :
    mobiusReciprocal * Mobius.mobiusScaling a = Mobius.mobiusScaling a⁻¹ * mobiusReciprocal := by
  apply Subtype.ext
  ext z
  cases z using OnePoint.rec with
  | infty =>
    change mobiusReciprocal.val ((Mobius.mobiusScaling a).val ∞) =
      (Mobius.mobiusScaling a⁻¹).val (mobiusReciprocal.val ∞)
    rw [Mobius.mobiusScaling_infty,mobiusReciprocal_infty,mobiusScaling_zero]
  | coe z =>
    change mobiusReciprocal.val ((Mobius.mobiusScaling a).val z) =
      (Mobius.mobiusScaling a⁻¹).val (mobiusReciprocal.val z)
    by_cases hz : z = 0
    · subst z
      rw [mobiusScaling_zero,mobiusReciprocal_zero,Mobius.mobiusScaling_infty]
    · rw [Mobius.mobiusScaling_coe,mobiusReciprocal_coe _ (mul_ne_zero (Units.ne_zero a) hz),
        mobiusReciprocal_coe z hz,Mobius.mobiusScaling_coe]
      simp only [Units.val_inv_eq_inv_val,mul_inv_rev,mul_comm]

theorem mobius_endpoint_exchange_square (f : Mobius.complexMobiusGroup)
    (hz : f.val (0 : ℂ) = ∞) (hi : f.val ∞ = (0 : ℂ)) : f*f=1 := by
  have hp : f ∈ mobiusZeroInftyPairStabilizer := by
    change f.val '' ({((0 : ℂ) : Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex) = _
    simp only [Set.image_insert_eq,Set.image_singleton,hz,hi,Set.pair_comm]
  obtain ⟨a,ha | ha⟩ := mobius_zeroInftyPair_normal_form ⟨f,hp⟩
  · change f = Mobius.mobiusScaling a at ha
    rw [ha,mobiusScaling_zero] at hz
    exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ)) hz)
  · change f = Mobius.mobiusScaling a * mobiusReciprocal at ha
    rw [ha]
    calc
      (Mobius.mobiusScaling a*mobiusReciprocal)*(Mobius.mobiusScaling a*mobiusReciprocal) =
          Mobius.mobiusScaling a*(mobiusReciprocal*Mobius.mobiusScaling a)*mobiusReciprocal := by
        group
      _ = Mobius.mobiusScaling a*(Mobius.mobiusScaling a⁻¹*mobiusReciprocal)*mobiusReciprocal := by
        rw [mobiusReciprocal_mul_scaling]
      _ = (Mobius.mobiusScaling a*Mobius.mobiusScaling a⁻¹)*(mobiusReciprocal*mobiusReciprocal) := by
        group
      _ = 1 := by
        rw [← mobiusScaling_mul,mul_inv_cancel,mobiusScaling_one,
          mobiusReciprocal_mul_self,one_mul]

theorem mobius_endpoint_exchange_inverts_scaling (f : Mobius.complexMobiusGroup)
    (hz : f.val (0 : ℂ) = ∞) (hi : f.val ∞ = (0 : ℂ)) (a : ℂˣ) :
    Mobius.mobiusScaling a*f=f*(Mobius.mobiusScaling a)⁻¹ := by
  have hp : f ∈ mobiusZeroInftyPairStabilizer := by
    change f.val '' ({((0 : ℂ) : Mobius.ExtendedComplex),∞} : Set Mobius.ExtendedComplex) = _
    simp only [Set.image_insert_eq,Set.image_singleton,hz,hi,Set.pair_comm]
  obtain ⟨b,hb | hb⟩ := mobius_zeroInftyPair_normal_form ⟨f,hp⟩
  · change f = Mobius.mobiusScaling b at hb
    rw [hb,mobiusScaling_zero] at hz
    exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ)) hz)
  · change f = Mobius.mobiusScaling b*mobiusReciprocal at hb
    rw [hb,mobiusScaling_inv,mul_assoc,mobiusReciprocal_mul_scaling,inv_inv,
      ← mul_assoc,← mul_assoc,← mobiusScaling_mul,← mobiusScaling_mul,mul_comm a b]

def mobiusEndpointKernel (H : Subgroup Mobius.complexMobiusGroup) : Subgroup H :=
  MulAction.stabilizer H ((0 : ℂ) : Mobius.ExtendedComplex)

theorem mobiusEndpointKernel_fixes_infty (H : Subgroup Mobius.complexMobiusGroup)
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (k : mobiusEndpointKernel H) :
    k.val.val.val ∞ = ∞ := by
  have hk : k.val.val.val (0 : ℂ) = (0 : ℂ) := k.property
  rcases mobius_zeroInftyPair_cases ⟨k.val.val,hp k.val.property⟩ with h | h
  · exact h.2
  · have he : ((0 : ℂ) : Mobius.ExtendedComplex) = ∞ := hk.symm.trans h.1
    exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ)) he)

theorem finiteMobius_endpointKernel_isCyclic (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hp : H ≤ mobiusZeroInftyPairStabilizer) : IsCyclic (mobiusEndpointKernel H) := by
  let K := mobiusEndpointKernel H
  let L := K.map H.subtype
  let e : K ≃* L := K.equivMapOfInjective H.subtype Subtype.val_injective
  have : Finite L := Finite.of_surjective e e.surjective
  have hi : L ≤ Mobius.mobiusInftyStabilizer := by
    rintro f ⟨g,hg,rfl⟩
    exact mobiusEndpointKernel_fixes_infty H hp ⟨g,hg⟩
  have hz : ∀ f ∈ L,f.val (0 : ℂ) = (0 : ℂ) := by
    rintro f ⟨g,hg,rfl⟩
    exact hg
  exact e.isCyclic.mpr (finiteMobius_fix_zero_infty_isCyclic L hi hz)

theorem mobiusEndpointKernel_exchange_relation (H : Subgroup Mobius.complexMobiusGroup)
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (s : H)
    (hsz : s.val.val (0 : ℂ) = ∞) (hsi : s.val.val ∞ = (0 : ℂ))
    (k : mobiusEndpointKernel H) : k.val*s=s*k.val⁻¹ := by
  have hkz : k.val.val.val (0 : ℂ) = (0 : ℂ) := k.property
  obtain ⟨a,ha⟩ := Mobius.mobius_fix_zero_infty_eq_scaling k.val.val hkz
    (mobiusEndpointKernel_fixes_infty H hp k)
  apply Subtype.ext
  change k.val.val*s.val=s.val*k.val.val⁻¹
  rw [ha]
  exact mobius_endpoint_exchange_inverts_scaling s.val hsz hsi a

theorem mobiusEndpointKernel_two_cosets (H : Subgroup Mobius.complexMobiusGroup)
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (s : H)
    (hsz : s.val.val (0 : ℂ) = ∞) (hsi : s.val.val ∞ = (0 : ℂ))
    (g : H) : g ∈ mobiusEndpointKernel H ∨ ∃ k : mobiusEndpointKernel H,g=s*k.val := by
  rcases mobius_zeroInftyPair_cases ⟨g.val,hp g.property⟩ with hg | hg
  · exact Or.inl hg.1
  · have hk : s*g ∈ mobiusEndpointKernel H := by
      change s • (g • ((0 : ℂ) : Mobius.ExtendedComplex)) = ((0 : ℂ) : Mobius.ExtendedComplex)
      have hg0 : g • ((0 : ℂ) : Mobius.ExtendedComplex) = ∞ := hg.1
      rw [hg0]
      exact hsi
    refine Or.inr ⟨⟨s*g,hk⟩,?_⟩
    have hs : s*s=1 := Subtype.ext (mobius_endpoint_exchange_square s.val hsz hsi)
    change g=s*(s*g)
    rw [← mul_assoc,hs,one_mul]

theorem mobiusEndpointKernel_exchange_orbit (H : Subgroup Mobius.complexMobiusGroup)
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (s : H)
    (hsz : s.val.val (0 : ℂ) = ∞) :
    MulAction.orbit H (((0 : ℂ) : Mobius.ExtendedComplex)) = {((0 : ℂ) : Mobius.ExtendedComplex),∞} := by
  ext z
  constructor
  · rintro ⟨g,rfl⟩
    rcases mobius_zeroInftyPair_cases ⟨g.val,hp g.property⟩ with hg | hg
    · exact Set.mem_insert_iff.mpr (Or.inl hg.1)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hg.1))
  · rintro (rfl | hz)
    · exact MulAction.mem_orbit_self _
    · have hz' : z = ∞ := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨s,hsz⟩

theorem finiteMobius_endpointKernel_order (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (s : H)
    (hsz : s.val.val (0 : ℂ) = ∞) : Nat.card H=2*Nat.card (mobiusEndpointKernel H) := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H
    (((0 : ℂ) : Mobius.ExtendedComplex)))
  rw [Nat.card_prod] at h
  have hc : Nat.card (MulAction.orbit H (((0 : ℂ) : Mobius.ExtendedComplex))) = 2 := by
    change (MulAction.orbit H (((0 : ℂ) : Mobius.ExtendedComplex))).ncard = 2
    rw [mobiusEndpointKernel_exchange_orbit H hp s hsz,
      Set.ncard_pair (OnePoint.coe_ne_infty (0 : ℂ))]
  rw [hc] at h
  exact h.symm

def finiteMobius_pair_dihedralEquiv (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hp : H ≤ mobiusZeroInftyPairStabilizer) (s : H)
    (hsz : s.val.val (0 : ℂ) = ∞) (hsi : s.val.val ∞ = (0 : ℂ)) :
    DihedralGroup (Nat.card (mobiusEndpointKernel H)) ≃* H := by
  have : IsCyclic (mobiusEndpointKernel H) := finiteMobius_endpointKernel_isCyclic H hp
  exact cyclicIndexTwoDihedralEquiv (mobiusEndpointKernel H) s
    (Subtype.ext (mobius_endpoint_exchange_square s.val hsz hsi))
    (mobiusEndpointKernel_exchange_relation H hp s hsz hsi)
    (mobiusEndpointKernel_two_cosets H hp s hsz hsi)
    (finiteMobius_endpointKernel_order H hp s hsz)

theorem mobiusVertex_orbit_image (H : Subgroup Mobius.complexMobiusGroup) (z : MobiusVertex H) :
    Subtype.val '' MulAction.orbit H z = MulAction.orbit H (z : Mobius.ExtendedComplex) := by
  ext w
  constructor
  · rintro ⟨v,⟨g,rfl⟩,rfl⟩
    exact ⟨g,rfl⟩
  · rintro ⟨g,rfl⟩
    exact ⟨g • z,MulAction.mem_orbit _ _,rfl⟩

theorem mobiusVertex_orbit_boundary_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) :
    Nat.card (MulAction.orbit H (z : Mobius.ExtendedComplex)) = Nat.card (MulAction.orbit H z) := by
  change (MulAction.orbit H (z : Mobius.ExtendedComplex)).ncard = (MulAction.orbit H z).ncard
  rw [← mobiusVertex_orbit_image H z]
  exact Set.ncard_image_of_injective _ Subtype.val_injective

theorem finiteMobius_two_point_orbit_dihedral (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : Mobius.ExtendedComplex) (ho : Nat.card (MulAction.orbit H z) = 2) :
    ∃ q : Mobius.complexMobiusGroup,∃ s : DiscreteGroups.Action.Actions.subgroupConjugate q H,
      DiscreteGroups.Action.Actions.subgroupConjugate q H ≤ mobiusZeroInftyPairStabilizer ∧
      s.val.val (0 : ℂ) = ∞ ∧ s.val.val ∞ = (0 : ℂ) := by
  obtain ⟨a,b,hab,horb⟩ := Set.ncard_eq_two.mp ho
  have ha : a ∈ MulAction.orbit H z := by rw [horb]; simp
  have hb : b ∈ MulAction.orbit H z := by rw [horb]; simp
  obtain ⟨ga,hga⟩ := ha
  obtain ⟨gb,hgb⟩ := hb
  let g : H := gb*ga⁻¹
  have hg : g • a=b := by
    rw [← hga]
    simp only [g,mul_smul,inv_smul_smul]
    exact hgb
  have hpair (f : H) : f.val.val '' {a,b} = {a,b} := by
    rw [← horb]
    ext w
    constructor
    · rintro ⟨v,⟨k,rfl⟩,rfl⟩
      exact ⟨f*k,mul_smul _ _ _⟩
    · rintro ⟨k,rfl⟩
      refine ⟨(f⁻¹*k) • z,⟨f⁻¹*k,rfl⟩,?_⟩
      change f • ((f⁻¹*k) • z)=k • z
      simp only [mul_smul,smul_inv_smul]
  obtain ⟨q,hqa,hqb⟩ := mobius_exists_send_pair_zero_infty a b hab
  have hp := mobius_subgroupConjugate_le_zeroInftyPairStabilizer H a b hpair q hqa hqb
  let s : DiscreteGroups.Action.Actions.subgroupConjugate q H :=
    DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g
  have hsz : s.val.val (0 : ℂ) = ∞ := by
    have hiq : q⁻¹ • (((0 : ℂ) : Mobius.ExtendedComplex)) = a := by
      change q • a = (((0 : ℂ) : Mobius.ExtendedComplex)) at hqa
      rw [← hqa,inv_smul_smul]
    change (q*g.val*q⁻¹) • (((0 : ℂ) : Mobius.ExtendedComplex)) = ∞
    simp only [mul_smul,hiq]
    change q • (g • a) = ∞
    rw [hg]
    exact hqb
  have hsi : s.val.val ∞ = (0 : ℂ) := by
    rcases mobius_zeroInftyPair_cases ⟨s.val,hp s.property⟩ with hs | hs
    · exact False.elim ((OnePoint.coe_ne_infty (0 : ℂ)) (hs.1.symm.trans hsz))
    · exact hs.2
  exact ⟨q,s,hp,hsz,hsi⟩

/-- The genuine `(2,2,n)` branch is isomorphic to the dihedral group. -/
theorem finiteMobius_dihedral_branch (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (o : MobiusVertexOrbit H) (n : ℕ) (hn : 2 ≤ n)
    (ho : mobiusVertexBranchOrder H o = n) (hh : Nat.card H=2*n) :
    Nonempty (H ≃* DihedralGroup n) := by
  have hs := finiteMobius_vertex_orbit_stabilizer H o.out
  change Nat.card (MulAction.orbit H o.out)*mobiusVertexBranchOrder H o=Nat.card H at hs
  rw [ho,hh] at hs
  have hc : Nat.card (MulAction.orbit H o.out)=2 := by nlinarith
  have hb : Nat.card (MulAction.orbit H (o.out : Mobius.ExtendedComplex))=2 := by
    rw [mobiusVertex_orbit_boundary_card,hc]
  obtain ⟨q,s,hp,hsz,hsi⟩ := finiteMobius_two_point_orbit_dihedral H o.out.val hb
  let K := DiscreteGroups.Action.Actions.subgroupConjugate q H
  let e : H ≃* K := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have : Finite K := Finite.of_surjective e e.surjective
  have hk : Nat.card K=Nat.card H := Nat.card_congr e.symm.toEquiv
  have horder := finiteMobius_endpointKernel_order K hp s hsz
  have hkn : Nat.card (mobiusEndpointKernel K)=n := by rw [hk,hh] at horder; omega
  have ed := finiteMobius_pair_dihedralEquiv K hp s hsz hsi
  rw [hkn] at ed
  exact ⟨e.trans ed.symm⟩

end LowDimensionalTopology.Geometry.DiscreteGroups
