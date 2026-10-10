import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralMarking

/-! Both physical marks determine the external tetrahedral frame. The proof
uses the current semantic O model, the actual T model and original reversal;
no coordinate conjugator is declared to be a realizable gate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionExternalTetrahedralFrame
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Projective.FiniteSubgroupClassification
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient

theorem tetrahedral_involution_pauli (q : modelPGL .tetrahedral)
    (ho : orderOf q=2) : (q : PGL2 ℂ) ∈ pauliSubgroup := by
  have hi := (involution_iff_orderOf (tetrahedral_iso_A4 q)).mpr
    ((tetrahedral_iso_A4.orderOf_eq q).trans ho)
  have hk := (a4_mem_kleinFour _).mpr (Or.inr hi)
  change q ∈ pauliSubgroup.subgroupOf (modelPGL .tetrahedral)
  rw [←tetrahedral_pauli_preimage]
  exact hk

theorem octahedral_outside_involution_transposition (q : modelPGL .octahedral)
    (ho : orderOf q=2) (hout : (q : PGL2 ℂ) ∉ modelPGL .tetrahedral) :
    Transposition (octahedral_iso_S4 q) := by
  have hi := (involution_iff_orderOf (octahedral_iso_S4 q)).mpr
    ((octahedral_iso_S4.orderOf_eq q).trans ho)
  rcases (s4_involution_types _).mp hi with hs | hd
  · exact hs
  · have hk := (s4_mem_kleinFour _).mpr (Or.inr hd)
    have hp : (q : PGL2 ℂ) ∈ pauliSubgroup := by
      change q ∈ pauliSubgroup.subgroupOf (modelPGL .octahedral)
      rw [←octahedral_pauli_preimage]
      exact hk
    exact (hout (pauli_le_model .tetrahedral hp)).elim

/-- Every commuting ordered (double-transposition,transposition) pair in
the literal O table has one actual O conjugator to indices (1,23).
Each branch is finite; neither current matrices nor their spans are tested
by this proposition. -/
theorem finite_pair_alignment (i j : Fin 24)
    (hi : i.val<4) (hi0 : i≠0)
    (hj : Transposition (fourPermutation j))
    (hc : Commute (fourPermutation i) (fourPermutation j)) :
    ∃ k : Fin 24,
      fourPermutation k * fourPermutation i * (fourPermutation k)⁻¹ = fourPermutation 1 ∧
      fourPermutation k * fourPermutation j * (fourPermutation k)⁻¹ = fourPermutation 23 := by
  have table : ∀ i : Fin 4, ∀ j : Fin 24, i≠0 →
      Transposition (fourPermutation j) →
      Commute (fourPermutation (i.castLE (by decide : 4≤24))) (fourPermutation j) →
      ∃ k : Fin 24,
        fourPermutation k * fourPermutation (i.castLE (by decide : 4≤24)) *
          (fourPermutation k)⁻¹ = fourPermutation 1 ∧
        fourPermutation k * fourPermutation j * (fourPermutation k)⁻¹ = fourPermutation 23 := by
    unfold Commute SemiconjBy
    decide +kernel
  have hz : (⟨i.val,hi⟩ : Fin 4)≠0 := by
    intro h
    apply hi0
    exact Fin.ext (congrArg (fun t : Fin 4=>t.val) h)
  exact table ⟨i.val,hi⟩ j hz hj hc

theorem literal_pair_alignment (x j : modelPGL .octahedral)
    (hx : (x : PGL2 ℂ) ∈ pauliSubgroup) (hx1 : (x : PGL2 ℂ)≠1)
    (hj : Transposition (octahedral_iso_S4 j)) (hc : Commute x j) :
    ∃ c : modelPGL .octahedral,
      c*x*c⁻¹=indexedPGL .octahedral (1 : Fin 24) ∧
      c*j*c⁻¹=indexedPGL .octahedral (23 : Fin 24) := by
  obtain ⟨i,rfl⟩ := indexedPGL_surjective .octahedral x
  obtain ⟨k,rfl⟩ := indexedPGL_surjective .octahedral j
  have hi := (indexed_mem_pauli_iff .octahedral i).mp hx
  have hi0 : i≠(0 : Fin 24) := by
    intro h
    apply hx1
    simpa [h,axisIndex] using indexed_axis_zero .octahedral
  have hj' : Transposition (fourPermutation k) := by simpa only [octahedral_iso_indexed] using hj
  have hc' : Commute (fourPermutation i) (fourPermutation k) := by
    have hh := hc.map octahedral_iso_S4.toMonoidHom
    change Commute (octahedral_iso_S4 (indexedPGL .octahedral i))
      (octahedral_iso_S4 (indexedPGL .octahedral k)) at hh
    simpa only [octahedral_iso_indexed] using hh
  obtain ⟨c,ha,hb⟩ := finite_pair_alignment i k hi hi0 hj' hc'
  refine ⟨indexedPGL .octahedral c,?_,?_⟩ <;>
    apply octahedral_iso_S4.injective
  · simpa only [map_mul,map_inv,octahedral_iso_indexed] using ha
  · simpa only [map_mul,map_inv,octahedral_iso_indexed] using hb

theorem map_conj_mul (H : Subgroup (PGL2 ℂ)) (g h : PGL2 ℂ) :
    H.map (MulAut.conj (g*h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext q
  change (g*h)*q*(g*h)⁻¹=g*(h*q*h⁻¹)*g⁻¹
  group

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (identity : (⟨2,binarySignature (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)

include identity in
theorem aligned
    (semantic : HasModel (overgroup phi F torsion) (.platonic .octahedral))
    (actual : HasModel (group phi F torsion) (.platonic .tetrahedral))
    (outside : zClass∉group phi F torsion) :
    ∃ g : PGL2 ℂ,
      (group phi F torsion).map (MulAut.conj g).toMonoidHom = modelPGL .tetrahedral ∧
      g*xClass*g⁻¹=xClass ∧
      g*zClass*g⁻¹=(indexedPGL .octahedral (23 : Fin 24) : PGL2 ℂ) := by
  obtain ⟨g,hJ⟩ := semantic
  have hcard : Nat.card (group phi F torsion)=12 := by
    obtain ⟨e⟩ := GlobalCloseCompletionTetrahedralMarking.model_equiv _ actual
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hH : (group phi F torsion).map (MulAut.conj g).toMonoidHom=modelPGL .tetrahedral := by
    apply subgroup_octahedral_card_twelve
    · rw [←hJ]
      exact Subgroup.map_mono (ClosureMarkedReversalOvergroup.actual_le _ _)
    · rw [card_conjugate_subgroup]
      exact hcard
  have hx0 := nativeX_mem phi F torsion identity
  have hxt : g*xClass*g⁻¹ ∈ modelPGL .tetrahedral := by
    rw [←hH]
    exact ⟨xClass,hx0,rfl⟩
  let tx : modelPGL .tetrahedral := ⟨g*xClass*g⁻¹,hxt⟩
  have hxorder : orderOf tx=2 := (Subgroup.orderOf_coe tx).symm.trans
    ((MulAut.conj g).orderOf_eq xClass |>.trans xClass_involution)
  let x : modelPGL .octahedral := ⟨g*xClass*g⁻¹,tetrahedral_le_octahedral hxt⟩
  have hjO : g*zClass*g⁻¹ ∈ modelPGL .octahedral := by
    rw [←hJ]
    refine ⟨zClass,?_,rfl⟩
    rw [←ClosureMarkedReversalOvergroup.Ambient.native_mark]
    exact ClosureMarkedReversalOvergroup.mark_mem _ _
  let j : modelPGL .octahedral := ⟨g*zClass*g⁻¹,hjO⟩
  have hjorder : orderOf j=2 := (Subgroup.orderOf_coe j).symm.trans
    ((MulAut.conj g).orderOf_eq zClass |>.trans zClass_involution)
  have hout : (j : PGL2 ℂ) ∉ modelPGL .tetrahedral := by
    intro hm
    rw [←hH] at hm
    obtain ⟨q,hq,heq⟩ := hm
    exact outside ((MulAut.conj g).injective heq ▸ hq)
  have hx1 : (x : PGL2 ℂ)≠1 := by
    intro hz
    exact pauli_x_ne_one ((MulAut.conj g).injective (by simpa [x] using hz))
  have hc : Commute x j := Subtype.ext
    ((xClass_commute_zClass.map (MulAut.conj g).toMonoidHom).eq)
  obtain ⟨c,ha,hb⟩ := literal_pair_alignment x j
    (tetrahedral_involution_pauli tx hxorder) hx1
    (octahedral_outside_involution_transposition j hjorder hout) hc
  have ha' := congrArg Subtype.val ha
  have hb' := congrArg Subtype.val hb
  refine ⟨(c : PGL2 ℂ)*g,?_,?_,?_⟩
  · rw [map_conj_mul,hH]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (octahedral_le_normalizer_tetrahedral c.property)
  · calc
      _ = (c : PGL2 ℂ)*(g*xClass*g⁻¹)*(c : PGL2 ℂ)⁻¹ := by group
      _ = xClass := ha'.trans (indexed_axis_one .octahedral)
  · calc
      _ = (c : PGL2 ℂ)*(g*zClass*g⁻¹)*(c : PGL2 ℂ)⁻¹ := by group
      _ = _ := hb'

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionExternalTetrahedralFrame
end
