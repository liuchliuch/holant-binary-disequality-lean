import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralMarking
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralLiteralDeck
import Holant.Projective.FiniteGroupFacts.IcosahedralNormalizer
import Holant.Certificates.OppositeIcosahedral.PhysicalDictionary

/-! The two literal actual I dictionaries are derived from the semantic
current marking and both native marks. These are analytic equalities of
complete source groups; no conjugating matrix becomes a gadget label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Projective.FiniteSubgroupClassification
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
open scoped BigOperators Matrix
local notation "Xₘ" => (Holant.Certificates.MatchingContractionClosure.X : ComplexMatrix)

namespace Placement
abbrev conjMap (n : PGL2 ℂ) := (MulAut.conj n).toMonoidHom

private theorem conjugate_twice (H : Subgroup (PGL2 ℂ)) (m n : PGL2 ℂ) :
    (H.map (conjMap n)).map (conjMap m) = H.map (conjMap (m*n)) := by
  rw [Subgroup.map_map]
  congr 1
  ext q
  change m * (n*q*n⁻¹) * m⁻¹ = (m*n)*q*(m*n)⁻¹
  group

private theorem undo_conjugate {H K : Subgroup (PGL2 ℂ)} {n : PGL2 ℂ}
    (h : H.map (conjMap n) = K) : K.map (conjMap n⁻¹) = H := by
  rw [←h,conjugate_twice]
  have hid : conjMap (n⁻¹*n)=MonoidHom.id (PGL2 ℂ) := by
    ext q
    simp [conjMap]
  rw [hid,Subgroup.map_id]

def DGL : ComplexGL := Matrix.GeneralLinearGroup.mkOfDetNeZero
  OppositeIcosahedral.D OppositeIcosahedral.D_det_ne_zero
def d : PGL2 ℂ := pglMk ℂ DGL
def oppositeGroup : Subgroup (PGL2 ℂ) := (modelPGL .icosahedral).map (conjMap d)

private theorem d_index : d = (indexedPGL .octahedral (16 : Fin 24) : PGL2 ℂ) := by
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨1,one_ne_zero,?_⟩
  change OppositeIcosahedral.D = 1 • representative .octahedral (16 : Fin 24)
  rw [one_smul]
  ext u v
  cases u <;> cases v <;>
    simp [OppositeIcosahedral.D,representative,raw,octahedralRaw,goldenMatrix,
      GoldenInt.eval,Holant.Certificates.MatchingProductBridge.quaternion,
      Matrix.smul_apply,smul_eq_mul,Q0,Q1,Q2,Q3,Signature.equality]

private theorem d_mem_octahedral : d ∈ modelPGL .octahedral := by
  rw [d_index]
  exact (indexedPGL .octahedral (16 : Fin 24)).property

private theorem d_inv_index : d⁻¹ = (indexedPGL .octahedral (17 : Fin 24) : PGL2 ℂ) := by
  apply inv_eq_of_mul_eq_one_right
  rw [d_index]
  have h := congrArg Subtype.val (indexedPGL_product .octahedral
    (16 : Fin 24) (17 : Fin 24))
  change (indexedPGL .octahedral (16 : Fin 24) : PGL2 ℂ) *
    (indexedPGL .octahedral (17 : Fin 24) : PGL2 ℂ) =
      (indexedPGL .octahedral (0 : Fin 24) : PGL2 ℂ) at h
  exact h.trans (congrArg Subtype.val (indexedPGL_identity .octahedral))

private theorem twelve_d_inv_tetrahedral :
    (indexedPGL .octahedral (12 : Fin 24) : PGL2 ℂ)*d⁻¹ ∈ modelPGL .tetrahedral := by
  rw [d_inv_index]
  have h := congrArg Subtype.val (indexedPGL_product .octahedral
    (12 : Fin 24) (17 : Fin 24))
  change (indexedPGL .octahedral (12 : Fin 24) : PGL2 ℂ) *
    (indexedPGL .octahedral (17 : Fin 24) : PGL2 ℂ) =
      (indexedPGL .octahedral (7 : Fin 24) : PGL2 ℂ) at h
  rw [h]
  refine ⟨representativeGL .octahedral (7 : Fin 24),?_,rfl⟩
  change groupDirection .tetrahedral (representative .octahedral (7 : Fin 24))
  have he : representative .octahedral (7 : Fin 24) =
      representative .tetrahedral (7 : Fin 12) := rfl
  rw [he]
  exact representative_mem .tetrahedral (7 : Fin 12)

private theorem d_not_tetrahedral : d ∉ modelPGL .tetrahedral := by
  intro hd
  have h := (modelPGL .tetrahedral).mul_mem twelve_d_inv_tetrahedral hd
  have hw : (indexedPGL .octahedral (12 : Fin 24) : PGL2 ℂ) ∈ modelPGL .tetrahedral := by
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using h
  exact octahedral_twelve_not_normalizer_icosahedral
    (tetrahedral_le_normalizer_icosahedral hw)

/-- The coset calculation is an equality of literal quotient subgroups.
The second coset is represented by the actual D=Q0+Q3, not by a free basis. -/
theorem octahedral_two_displays {n : PGL2 ℂ} (hn : n ∈ modelPGL .octahedral) :
    (modelPGL .icosahedral).map (conjMap n) = modelPGL .icosahedral ∨
      (modelPGL .icosahedral).map (conjMap n) = oppositeGroup := by
  classical
  by_cases ht : n ∈ modelPGL .tetrahedral
  · exact Or.inl (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (tetrahedral_le_normalizer_icosahedral ht))
  · let T := (modelPGL .tetrahedral).subgroupOf (modelPGL .octahedral)
    let ni : modelPGL .octahedral := ⟨n,hn⟩
    let di : modelPGL .octahedral := ⟨d,d_mem_octahedral⟩
    have hdi : di⁻¹ ∉ T := by
      intro hi
      apply d_not_tetrahedral
      have hi' : d⁻¹ ∈ modelPGL .tetrahedral := hi
      have hh := (modelPGL .tetrahedral).inv_mem hi'
      simpa only [inv_inv] using hh
    have hni : ni ∉ T := ht
    have hp : di⁻¹*ni ∈ T :=
      (T.mul_mem_iff_of_index_two tetrahedral_index_in_octahedral).mpr
        (by simp only [hdi,hni])
    have ht' : d⁻¹*n ∈ Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) :=
      tetrahedral_le_normalizer_icosahedral hp
    have hm := Subgroup.mem_normalizer_iff_map_conj_eq.mp ht'
    change (modelPGL .icosahedral).map (conjMap (d⁻¹*n))=modelPGL .icosahedral at hm
    have hh := congrArg (fun H : Subgroup (PGL2 ℂ) => H.map (conjMap d)) hm
    rw [conjugate_twice] at hh
    right
    simpa only [mul_inv_cancel_left,oppositeGroup] using hh

/-- A corrected conjugator centralizes x and belongs to the actual O.
The equality of its Pauli image uses the proved four-element cardinality;
mere containment in O is never used to assert a group equality. -/
theorem correct_conjugator {H : Subgroup (PGL2 ℂ)}
    (hp : pauliSubgroup ≤ H) {b : PGL2 ℂ}
    (hb : H.map (conjMap b) = modelPGL .icosahedral) :
    ∃ n : PGL2 ℂ, n ∈ modelPGL .octahedral ∧
      H.map (conjMap n) = modelPGL .icosahedral ∧ n*xClass*n⁻¹=xClass := by
  letI : Finite pauliSubgroup := Nat.finite_of_card_ne_zero (by rw [pauli_card]; decide)
  let y : modelPGL .icosahedral := ⟨b*xClass*b⁻¹,by
    rw [←hb]
    exact ⟨xClass,hp xClass_mem_pauli,rfl⟩⟩
  have hy : orderOf y = 2 := by
    rw [←Subgroup.orderOf_coe]
    change orderOf ((MulAut.conj b) xClass) = 2
    rw [MulEquiv.orderOf_eq]
    exact xClass_involution
  have hxA : Involution (icosahedral_iso_A5 icosahedralX) := by
    rw [involution_iff_orderOf,MulEquiv.orderOf_eq]
    exact icosahedralX_order
  have hyA : Involution (icosahedral_iso_A5 y) := by
    rw [involution_iff_orderOf,MulEquiv.orderOf_eq]
    exact hy
  obtain ⟨c,hc⟩ := isConj_iff.mp (a5_involutions_one_class _ _ hxA hyA)
  let i := icosahedral_iso_A5.symm c
  have hi : (i : PGL2 ℂ)*xClass*(i : PGL2 ℂ)⁻¹=b*xClass*b⁻¹ := by
    have he : i*icosahedralX*i⁻¹=y := by
      apply icosahedral_iso_A5.injective
      simpa only [i,map_mul,map_inv,MulEquiv.apply_symm_apply] using hc
    exact congrArg Subtype.val he
  let n : PGL2 ℂ := (i : PGL2 ℂ)⁻¹*b
  have hnx : n*xClass*n⁻¹=xClass := by
    calc
      _ = (i : PGL2 ℂ)⁻¹*(b*xClass*b⁻¹)*i := by dsimp [n]; group
      _ = xClass := by rw [←hi]; group
  have hnH : H.map (conjMap n) = modelPGL .icosahedral := by
    have hm := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((modelPGL .icosahedral).le_normalizer ((modelPGL .icosahedral).inv_mem i.property))
    rw [show n=(i : PGL2 ℂ)⁻¹*b from rfl,←conjugate_twice,hb]
    exact hm
  have hle : pauliSubgroup.map (conjMap n) ≤ pauliSubgroup := by
    rintro q ⟨r,hr,rfl⟩
    have hm : n*r*n⁻¹ ∈ modelPGL .icosahedral := by
      rw [←hnH]
      exact ⟨r,hp hr,rfl⟩
    have hx : Commute r xClass := ((commute_x_z_iff r).mpr ((pauli_membership r).mp hr)).1
    have hc' := hx.map (conjMap n)
    have he : Commute (n*r*n⁻¹) xClass := by
      change Commute (n*r*n⁻¹) (n*xClass*n⁻¹) at hc'
      rwa [hnx] at hc'
    rw [←icosahedral_inf_centralizer_x]
    exact ⟨hm,Subgroup.mem_centralizer_singleton_iff.mpr he.eq⟩
  have hcard : Nat.card (pauliSubgroup.map (conjMap n)) = Nat.card pauliSubgroup :=
    (Nat.card_congr (pauliSubgroup.equivMapOfInjective (conjMap n)
      (MulAut.conj n).injective).toEquiv).symm
  have he : pauliSubgroup.map (conjMap n) = pauliSubgroup :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hnP : n ∈ Subgroup.normalizer (pauliSubgroup : Set (PGL2 ℂ)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr he
  exact ⟨n,pauli_normalizer ▸ hnP,hnH,hnx⟩

theorem pauli_two_displays (H : Subgroup (PGL2 ℂ)) (hp : pauliSubgroup≤H)
    (model : HasModel H (.platonic .icosahedral)) :
    H=modelPGL .icosahedral ∨ H=oppositeGroup := by
  obtain ⟨b,hb⟩ := model
  obtain ⟨n,hn,hg,_⟩ := correct_conjugator hp hb
  have he := undo_conjugate hg
  have hrow := octahedral_two_displays ((modelPGL .octahedral).inv_mem hn)
  rw [he] at hrow
  exact hrow

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)

theorem semantic_actual
    (semantic : HasModel (overgroup phi F torsion) (.platonic .icosahedral)) :
    group phi F torsion=overgroup phi F torsion := by
  have hc : Nat.card (overgroup phi F torsion)≤2*Nat.card (group phi F torsion) := by
    rw [source_cardinal]
    exact cardinal_original phi F torsion
  obtain ⟨p,hp,g,hk,hh⟩ := ClosureMarkedPlatonicSubgroup.actual_model
    (group phi F torsion) (overgroup phi F torsion)
    (ClosureMarkedReversalOvergroup.actual_le _ _) hc .icosahedral semantic
  have hp' : p=.icosahedral := by
    rcases hp with hp | ⟨impossible,_⟩
    · exact hp
    · cases impossible
  subst p
  exact Subgroup.map_injective (MulAut.conj g).injective (hh.trans hk.symm)

theorem current_two_displays
    (identity : (⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)
    (semantic : HasModel (overgroup phi F torsion) (.platonic .icosahedral)) :
    group phi F torsion=modelPGL .icosahedral ∨ group phi F torsion=oppositeGroup := by
  have same := semantic_actual phi F torsion semantic
  apply pauli_two_displays
  · rw [same]
    exact ClosureMarkedReversalOvergroup.Ambient.pauli_le phi F torsion identity
  · exact same.symm ▸ semantic
end Placement

namespace Dictionary
private theorem matrix_X_eq_product :
    Xₘ=(Holant.Certificates.MatchingProductBridge.X : ComplexMatrix) := by
  ext u v
  rfl

private theorem matrix_X_eq_opposite : Xₘ=OppositeIcosahedral.X := by
  ext u v
  rfl

def group (opposite : Bool) : Subgroup (PGL2 ℂ) :=
  if opposite then Placement.oppositeGroup else modelPGL .icosahedral
def direction (opposite : Bool) (K : ComplexMatrix) : Prop :=
  if opposite then OppositeIcosahedral.Direction K else groupDirection .icosahedral K
def kernel (opposite : Bool) (i : Fin 60) : ComplexMatrix :=
  if opposite then OppositeIcosahedral.kappa (OppositeIcosahedral.standardRepresentative i)
  else OppositeIcosahedral.standardRepresentative i

private theorem DGL_inverse : (↑Placement.DGL⁻¹ : ComplexMatrix) = OppositeIcosahedral.Dinv := by
  calc
    _ = (↑Placement.DGL⁻¹ : ComplexMatrix) *
        (OppositeIcosahedral.D * OppositeIcosahedral.Dinv) := by
      rw [OppositeIcosahedral.D_Dinv,Matrix.mul_one]
    _ = ((↑Placement.DGL⁻¹ : ComplexMatrix) * OppositeIcosahedral.D) *
        OppositeIcosahedral.Dinv := (Matrix.mul_assoc _ _ _).symm
    _ = OppositeIcosahedral.Dinv := by
      rw [show (↑Placement.DGL⁻¹ : ComplexMatrix)*OppositeIcosahedral.D=1 from
        Placement.DGL.inv_val,Matrix.one_mul]

theorem matrix_iff (opposite : Bool) (U : ComplexGL) :
    pglMk ℂ U ∈ group opposite ↔ direction opposite U := by
  cases opposite
  · exact pglMk_mem_model_iff .icosahedral U
  · change pglMk ℂ U ∈ (modelPGL .icosahedral).map (Placement.conjMap Placement.d) ↔
      OppositeIcosahedral.Direction (U : ComplexMatrix)
    rw [Subgroup.map_equiv_eq_comap_symm']
    change (MulAut.conj Placement.d).symm (pglMk ℂ U) ∈ modelPGL .icosahedral ↔ _
    have he : (MulAut.conj Placement.d).symm (pglMk ℂ U) =
        pglMk ℂ (Placement.DGL⁻¹*U*Placement.DGL) := by
      change (pglMk ℂ Placement.DGL)⁻¹*pglMk ℂ U*pglMk ℂ Placement.DGL = _
      rw [map_mul,map_mul,map_inv]
    rw [he,pglMk_mem_model_iff]
    have hm : (↑(Placement.DGL⁻¹*U*Placement.DGL) : ComplexMatrix) =
        OppositeIcosahedral.pull (U : ComplexMatrix) := by
      simp only [Units.val_mul,DGL_inverse]
      rfl
    rw [hm]
    constructor
    · intro h
      have hh := OppositeIcosahedral.conjugate_standard h
      rwa [OppositeIcosahedral.conjugate_pull] at hh
    · exact OppositeIcosahedral.pull_opposite

theorem kernel_mem (opposite : Bool) (i : Fin 60) : direction opposite (kernel opposite i) := by
  cases opposite
  · exact OppositeIcosahedral.standardRepresentative_mem i
  · exact (OppositeIcosahedral.kernel_membership_iff _).mpr
      (OppositeIcosahedral.standardRepresentative_mem i)

theorem kernel_projectively_injective (opposite : Bool) (i j : Fin 60) (c : ℂ)
    (h : kernel opposite i=c • kernel opposite j) : i=j := by
  cases opposite
  · exact RainbowOrbit.projectively_injective .icosahedral i j c h
  · apply RainbowOrbit.projectively_injective .icosahedral i j c
    apply OppositeIcosahedral.kappa_injective
    rw [OppositeIcosahedral.kappa_smul]
    exact h

theorem group_card (opposite : Bool) : Nat.card (group opposite) = 60 := by
  cases opposite
  · exact modelPGL_card .icosahedral
  · change Nat.card ((modelPGL .icosahedral).map (Placement.conjMap Placement.d))=60
    rw [←Nat.card_congr ((modelPGL .icosahedral).equivMapOfInjective
      (Placement.conjMap Placement.d) (MulAut.conj Placement.d).injective).toEquiv]
    exact modelPGL_card .icosahedral

theorem complete (opposite : Bool) (K : ComplexMatrix) (hK : direction opposite K) :
    ∃ i : Fin 60, ∃ c : ℂ, c ≠ 0 ∧ K=c • kernel opposite i := by
  cases opposite
  · exact (RainbowOrbit.complete .icosahedral K).mp hK
  · obtain ⟨j,c,hc,he⟩ := (OppositeIcosahedral.direction_complete K).mp hK
    obtain ⟨i,hi⟩ := OppositeIcosahedral.kernelIndex_bijective.surjective j
    refine ⟨i,c/OppositeIcosahedral.kernelScale i,
      div_ne_zero hc (OppositeIcosahedral.kernelScale_ne_zero i),?_⟩
    change K=(c/OppositeIcosahedral.kernelScale i) •
      OppositeIcosahedral.kappa (OppositeIcosahedral.standardRepresentative i)
    rw [OppositeIcosahedral.kernel_representative_exact,hi,smul_smul,
      div_mul_cancel₀ _ (OppositeIcosahedral.kernelScale_ne_zero i)]
    exact he

theorem scale (opposite : Bool) {K : ComplexMatrix} (hK : direction opposite K)
    {c : ℂ} (hc : c ≠ 0) : direction opposite (c • K) := by
  cases opposite
  · exact groupDirection_smul .icosahedral hK hc
  · exact OppositeIcosahedral.Direction.smul hK hc

theorem right_X (opposite : Bool) (K : ComplexMatrix) :
    direction opposite (K*Xₘ) ↔ direction opposite K := by
  cases opposite
  · change groupDirection .icosahedral (K*Xₘ) ↔ groupDirection .icosahedral K
    have hm : (K*Xₘ : Matrix Bool Bool ℂ) =
        Holant.Certificates.MatchingProductBridge.multiply K
          Holant.Certificates.MatchingProductBridge.X := by
      ext u v
      cases u <;> cases v <;>
        simp [Matrix.mul_apply,Holant.Certificates.MatchingContractionClosure.X,
          Holant.Certificates.MatchingProductBridge.multiply,
          Holant.Certificates.MatchingProductBridge.X,Signature.disequality]
    rw [hm]
    exact groupDirection_right_X_iff .icosahedral K
  · change OppositeIcosahedral.Direction (K*Xₘ) ↔ OppositeIcosahedral.Direction K
    constructor
    · intro h
      have hh := h.mul OppositeIcosahedral.direction_X
      rw [←matrix_X_eq_opposite,Matrix.mul_assoc,
        Holant.Certificates.MatchingContractionClosure.X_mul_X,Matrix.mul_one] at hh
      exact hh
    · intro h
      have hh := h.mul OppositeIcosahedral.direction_X
      rw [←matrix_X_eq_opposite] at hh
      exact hh

theorem kernel_transfer (opposite : Bool) (i : Fin 60) :
    direction opposite (transfer (nativePair (kernel opposite i))) := by
  cases opposite
  · have hX : groupDirection .icosahedral Xₘ := by
      rw [matrix_X_eq_product]
      exact X_direction .icosahedral
    have hK := kernel_mem false i
    have he : transfer (nativePair (kernel false i)) = Xₘ * kernel false i := by
      simp only [transfer,nativePair,Matrix.mul_assoc,X_mul_X,Matrix.mul_one]
    rw [he]
    exact groupDirection_mul .icosahedral hX hK
  · exact (OppositeIcosahedral.native_pair_direction (kernel_mem true i)).2

def safe (opposite : Bool) (B : ComplexMatrix) : Prop := B=0 ∨ direction opposite B
theorem safe_scale (opposite : Bool) (c : ℂ) (hc : c ≠ 0) (B : ComplexMatrix) :
    safe opposite (c • B) ↔ safe opposite B := by
  constructor
  · rintro (hz | hg)
    · exact Or.inl ((smul_eq_zero.mp hz).resolve_left hc)
    · have hh := scale opposite hg (inv_ne_zero hc)
      exact Or.inr (by simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh)
  · rintro (rfl | hg)
    · exact Or.inl (smul_zero _)
    · exact Or.inr (scale opposite hg hc)
end Dictionary
namespace Preserver
open Holant.Certificates.TetrahedralPreservers Holant.Certificates.PlatonicIncidence
open GlobalCloseCompletionTetrahedralLiteralDeck
def roots (opposite : Bool) : Set V := CoefficientSet {K | Dictionary.direction opposite K}
def LiteralDeck (opposite : Bool) (q : FourTensor) : Prop :=
  ∀ e : Equiv.Perm (Fin 4), ∀ K : ComplexMatrix, Dictionary.direction opposite K →
    Dictionary.safe opposite (GlobalCloseCompletionTetrahedralLiteralDeck.rawCard q e K)

private theorem reindex_deck (opposite : Bool) (q : FourTensor) (h : LiteralDeck opposite q)
    (e : Equiv.Perm (Fin 4)) : LiteralDeck opposite (relabel e q) := by
  intro d K hK
  have same : GlobalCloseCompletionTetrahedralLiteralDeck.rawCard (relabel e q) d K =
      GlobalCloseCompletionTetrahedralLiteralDeck.rawCard q (d.trans e) K := by
    unfold GlobalCloseCompletionTetrahedralLiteralDeck.rawCard
    rw [relabel_relabel]
  rw [same]
  exact h (d.trans e) K hK

private theorem one_sided (opposite : Bool) (q : FourTensor) (h : LiteralDeck opposite q) :
    OneSided (roots opposite) (cardMatrix q) := by
  intro v hv
  have hK : Dictionary.direction opposite (assemble v) :=
    (mem_coefficientSet_iff _ v).mp hv
  have ha : cardMatrix q *ᵥ v = coordinates
      (GlobalCloseCompletionTetrahedralLiteralDeck.rawCard q (Equiv.refl _) (assemble v)) := by
    have hc : coordinates (assemble v) = v := coefficient_assemble v
    simpa only [hc] using cardMatrix_action q (assemble v)
  rw [ha]
  rcases h (Equiv.refl _) (assemble v) hK with hz | hg
  · exact Or.inl (by rw [hz,map_zero])
  · exact Or.inr ⟨_,hg,rfl⟩

/-- Both complementary physical port pairs give the ORIGINAL bilinear
Frobenius sharp J Aᵀ J. This does not assume the H4 preserver classification. -/
theorem two_sided (opposite : Bool) (q : FourTensor) (h : LiteralDeck opposite q) :
    TwoSided (roots opposite) (cardMatrix q) := by
  refine ⟨one_sided opposite q h,?_⟩
  rw [←cardMatrix_complement]
  exact one_sided opposite _ (reindex_deck opposite q h blockSwap)
end Preserver


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral
end
