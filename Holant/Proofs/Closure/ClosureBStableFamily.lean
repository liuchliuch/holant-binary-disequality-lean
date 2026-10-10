import Holant.Proofs.Closure.ClosureBStableDeck
import Holant.Proofs.Closure.ClosureBStableFactor
import Holant.Proofs.Closure.ClosureCompatibleAlignmentOneStep
import Holant.Proofs.Closure.ClosureProgramStability

/-! Every nonzero transformed M sample keeps the original CURRENT native
matching witness and source key. Matching equality comes from the original
stable deck; fixed-line distance comes from the proved transformed root deck.
No transformed Palette, field re-extraction, alignment or compiler is input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine Holant.Dihedral.TwoCardLocalization
open ClosureCompatibleAlignment Holant.Dihedral.EndpointParallelogram

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable {r : ℕ} (f : Signature (OI.K G) (2*r+4)) (order : Equiv.Perm (Fin (2*r+4)))
variable (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)

def sampleTensor : Signature Scalar (2*r+4) := Tensor.reindex order.symm (transformed G f)
abbrev Sample := ClosureBStableFactor.Sample N.selected.m r (sampleTensor G f order)

structure Selected (i : Sample G P torsion N f order) where
  native : Presentation (OI.K G) (Fin (2*r+2))
  valid : native.Valid (actualTransfers P.family)
  nonzero : native.scalar≠0
  equation : Signature.contract (currentKernel G P torsion N i.val.1 i.val.2) (Tensor.reindex order.symm f)=native.tensor

def selected (i : Sample G P torsion N f order) : Selected G P torsion N f order i := by
  let key := DeckContraction.orderedKey P.family torsion order (phaseIndex G P torsion N i.val.1 i.val.2).key
  have live : rawCard P.family torsion f key≠0 := by
    intro zero
    have h := ordered_card_identity G P torsion N f order i.val.1 i.val.2
    change transformed G (rawCard P.family torsion f key)=_ at h
    rw [zero] at h
    have transformedZero : transformed G (0 : Signature (OI.K G) (2*r+2))=0 := by
      have mapped : RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (0 : Signature (OI.K G) (2*r+2))=0 := by
        funext x; exact map_zero _
      rw [transformed,mapped,ClosureFactorTreeAction.action_zero]
    rw [transformedZero] at h
    exact i.property ((smul_eq_zero.mp h.symm).resolve_left (cardCoefficient_nonzero G P torsion N i.val.1 i.val.2))
  have actual := (stable _ (Or.inr ⟨key,rfl⟩)).resolve_left live
  let Q := Classical.choose actual
  have spec := Classical.choose_spec actual
  refine ⟨Q,spec.1,spec.2.1,?_⟩
  have identity : rawCard P.family torsion f key=Signature.contract
    (currentKernel G P torsion N i.val.1 i.val.2) (Tensor.reindex order.symm f) :=
    DeckContraction.rawCard_ordered P.family torsion f order (phaseIndex G P torsion N i.val.1 i.val.2).key
  exact identity.symm.trans spec.2.2

namespace Selected
variable {G P torsion N f order}
variable {i : Sample G P torsion N f order} (S : Selected G P torsion N f order i)

def algebraic : Presentation Scalar (Fin (2*r+2)) :=
  let Q := HistorySectorCards.matching (ClosureSourceRows.embedding G) basisB S.native
  {Q with scalar := (cardCoefficient G P torsion N i.val.1 i.val.2)⁻¹ * Q.scalar}

theorem scalar_nonzero : S.algebraic.scalar≠0 :=
  mul_ne_zero (inv_ne_zero (cardCoefficient_nonzero G P torsion N i.val.1 i.val.2)) ((map_ne_zero _).mpr S.nonzero)

theorem member (e : Fin S.algebraic.edges) : S.algebraic.matrix e ∈ groupM N.selected.m :=
  matching_factor_groupM G P torsion N S.native S.valid e

set_option backward.isDefEq.respectTransparency false in
theorem algebraic_equation : Signature.contract (M i.val.1 i.val.2.val) (sampleTensor G f order)=S.algebraic.tensor := by
  let c := cardCoefficient G P torsion N i.val.1 i.val.2
  have cn : c≠0 := cardCoefficient_nonzero G P torsion N i.val.1 i.val.2
  have h := ordered_card_identity G P torsion N f order i.val.1 i.val.2
  rw [DeckContraction.rawCard_ordered] at h
  change transformed G (Signature.contract (currentKernel G P torsion N i.val.1 i.val.2)
    (Tensor.reindex order.symm f))=c • Signature.contract (M i.val.1 i.val.2.val) (sampleTensor G f order) at h
  rw [S.equation] at h
  dsimp only [transformed] at h
  rw [HistorySectorCards.matching_tensor] at h
  have inverse := congrArg (fun q : Signature Scalar (2*r+2) => c⁻¹ • q) h
  simp only [smul_smul,inv_mul_cancel₀ cn,one_smul] at inverse
  rw [←inverse]
  funext x
  simp only [algebraic,Presentation.tensor,Holant.Certificates.MatchingContractionClosure.productValue,
    Pi.smul_apply,smul_eq_mul,mul_assoc]
  rfl

theorem edgeCount : S.native.edges=r+1 := by
  have h := Fintype.card_congr S.native.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  omega

def ports : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (Equiv.prodCongr (finCongr S.edgeCount).symm (Equiv.refl Bool)).trans S.native.ports

def factors (e : Fin (r+1)) : Mat := S.algebraic.matrix ((finCongr S.edgeCount).symm e)

theorem factors_member (e : Fin (r+1)) : S.factors e ∈ groupM N.selected.m := S.member _

theorem coefficient_product : Signature.contract (M i.val.1 i.val.2.val) (sampleTensor G f order)=
    Holant.Dihedral.CompatibleClosure.productValue S.ports S.factors S.algebraic.scalar := by
  rw [S.algebraic_equation]
  funext x
  apply congrArg (S.algebraic.scalar* ·)
  exact (Equiv.prod_comp (finCongr S.edgeCount).symm
    (fun e => S.algebraic.matrix e (x (S.native.ports (e,false))) (x (S.native.ports (e,true))))).symm

theorem pairing_native : (Pairing.ofPorts S.ports).mate=(presentationMatching S.native).mate := by
  funext u
  simp [ports,Pairing.ofPorts,presentationMatching,Holant.Pauli.ExoticKlein.Matching.mate]
  rfl

end Selected

theorem selected_matchings_equal (large : 2≤r) (i j : Sample G P torsion N f order) :
    (Pairing.ofPorts (selected G P torsion N f order stable i).ports).mate=
      (Pairing.ofPorts (selected G P torsion N f order stable j).ports).mate := by
  rw [Selected.pairing_native,Selected.pairing_native]
  let A := selected G P torsion N f order stable i
  let B := selected G P torsion N f order stable j
  have forbidden := ClosureProgramStability.stable_even_ordered_cards_not_different P.family torsion
    (P.retainsIdentity G) (by omega : 6≤2*r+2) (by exact ⟨r+1,by omega⟩ : Even (2*r+2)) f stable order
    (currentKernel G P torsion N i.val.1 i.val.2) (currentKernel G P torsion N j.val.1 j.val.2)
  have same : (presentationMatching A.native).mate=(presentationMatching B.native).mate := by
    by_contra different
    exact forbidden ⟨A.native,B.native,A.valid,B.valid,A.nonzero,B.nonzero,A.equation,B.equation,different⟩
  exact congrArg (fun e : Equiv.Perm (Fin (2*r+2)) => e.toFun) same

variable (anchor : Sample G P torsion N f order)
def familyPorts : (Fin (r+1) × Bool) ≃ Fin (2*r+2) := (selected G P torsion N f order stable anchor).ports
def familyTables (i : Sample G P torsion N f order) : Fin (r+1) → Mat :=
  alignedFactor (familyPorts G P torsion N f order stable anchor)
    (selected G P torsion N f order stable i).ports (selected G P torsion N f order stable i).factors
def familyCoefficient (i : Sample G P torsion N f order) : Scalar := (selected G P torsion N f order stable i).algebraic.scalar

theorem family_member (i : Sample G P torsion N f order) (e : Fin (r+1)) :
    familyTables G P torsion N f order stable anchor i e ∈ groupM N.selected.m :=
  alignedFactor_group (by have := N.selected.range; omega) _ _ _ (selected G P torsion N f order stable i).factors_member e

theorem family_equation (large : 2≤r) (i : Sample G P torsion N f order) :
    Signature.contract (M i.val.1 i.val.2.val) (sampleTensor G f order)=
      Holant.Dihedral.CompatibleClosure.productValue (familyPorts G P torsion N f order stable anchor)
        (familyTables G P torsion N f order stable anchor i) (familyCoefficient G P torsion N f order stable i) := by
  let A := selected G P torsion N f order stable anchor
  let B := selected G P torsion N f order stable i
  have same := selected_matchings_equal G P torsion N f order stable large anchor i
  have h := B.coefficient_product
  rw [←aligned_product A.ports B.ports same B.factors B.algebraic.scalar] at h
  exact h

include stable in
theorem outside_root_cases (cut : Equiv.Perm (Fin (2*r+2))) (p : Bool) (t : {t : Scalar // Roots N.selected.m t}) :
    outsideClose cut (M p t.val) (sampleTensor G f order)=0 ∨
      ClosureSixPort.AlgebraicRootMatching N.selected.m (outsideClose cut (M p t.val) (sampleTensor G f order)) :=
  ordered_root_deck G P torsion N f stable ((outsideOrder cut).trans order) p t

theorem family_distance (large : 2≤r) (i j : Sample G P torsion N f order)
    (e d : Fin (r+1)) (different : e≠d) :
    ProjectivelyEqual (familyTables G P torsion N f order stable anchor j e)
      (familyTables G P torsion N f order stable anchor i e) ∨
    ProjectivelyEqual (familyTables G P torsion N f order stable anchor j d)
      (familyTables G P torsion N f order stable anchor i d) :=
  common_matching_one_step_bound N.selected.range large _
    (outside_root_cases G P torsion N f order stable)
    _ _ (familyPorts G P torsion N f order stable anchor)
    (familyTables G P torsion N f order stable anchor i) (familyTables G P torsion N f order stable anchor j)
    _ _ (family_member G P torsion N f order stable anchor i) (family_member G P torsion N f order stable anchor j)
    (selected G P torsion N f order stable i).scalar_nonzero (selected G P torsion N f order stable j).scalar_nonzero
    (family_equation G P torsion N f order stable anchor large i) (family_equation G P torsion N f order stable anchor large j)
    e d different

def family (large : 2≤r) : ClosureBStableFactor.Family N.selected.m r (sampleTensor G f order) where
  anchor := anchor
  ports := familyPorts G P torsion N f order stable anchor
  tables := familyTables G P torsion N f order stable anchor
  coefficient := familyCoefficient G P torsion N f order stable
  equation := family_equation G P torsion N f order stable anchor large
  distance := family_distance G P torsion N f order stable anchor large

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
