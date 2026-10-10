import Holant.Proofs.FiniteGroups.Stabilization.LeafExposure
import Holant.Proofs.Reductions.FactorSaturation.Reconstruction

/-! Generic actual direct networks and data-valued exact saved-slot splits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant Holant.Algebraic Holant.Complexity Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.Certificates.MatchingContractionClosure

/-- An actual fixed ordinary network, with all source labels and native edges
verified. This is data, rather than an existential Realizes-only interface. -/
structure DeckDirect {L : Type} [Field L] (F : SignatureFamily L)
    {n : ℕ} (f : Signature L n) where
  network : Network L n
  vertex : ∀ v, (⟨network.shape.arity v, network.vertex v⟩ : AnySignature L) ∈ F
  edge : ∀ e, network.edge e = Signature.disequality
  value : network.denote = f

namespace DeckDirect

variable {L : Type} [Field L] {F : SignatureFamily L} {n : ℕ} {f : Signature L n}

def ofRealizes (hI : RetainsIdentity F) (hf : Gadget.Realizes F .disequality f) :
    DeckDirect F f := by
  let h := OrdinaryNormalization.realizes_exists_ordinary hI hf
  exact ⟨Classical.choose h,(Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1,(Classical.choose_spec h).2.2⟩


theorem realizes (D : DeckDirect F f) : Gadget.Realizes F .disequality f := by
  have h := Gadget.realizes_network D.network F .disequality D.vertex D.edge
  rwa [D.value] at h

/-- The single-copy boundary bijection retains every port occurrence. -/
def oneCopyPorts (n : ℕ) : Fin n ≃ Fin (1*n) where
  toFun i := finProdFinEquiv (0,i)
  invFun i := (finProdFinEquiv.symm i).2
  left_inv i := by simp
  right_inv i := by
    apply finProdFinEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl

/-- A direct graph is a genuine exponent-one macro, with source labels
physically installed; it does not gain an uncharged new label. -/
def directPower {k : ℕ} {A : ℕ → ℕ}
    (T : (i : Fin k) → Signature L (A i.val))
    (hI : RetainsIdentity (Set.range (fun i => (⟨A i.val,T i⟩ : AnySignature L))))
    (hf : Gadget.Realizes (Set.range (fun i => (⟨A i.val,T i⟩ : AnySignature L)))
      .disequality f) : GeneralPowerExposure.PowerMacro T f := by
  let D := ofRealizes hI (realizes_reindex_equiv _ (oneCopyPorts n) f hf)
  let lab := Holant.Complexity.BinaryInterpolation.Chains.labellingOfUses A T
    D.network D.vertex (0 : Fin 1)
  refine ⟨1,by omega,1,one_ne_zero,D.network,lab,?_⟩
  have hv := Holant.Complexity.BinaryInterpolation.Chains.labellingOfUses_denote
    A T D.network D.vertex D.edge (0 : Fin 1) (fun _ => Signature.disequality) rfl
  rw [hv,D.value]
  funext x
  change f (fun i => x (finProdFinEquiv (0,i))) = 1 * Carrier.blockPower f 1 x
  rw [Carrier.blockPower_one]
  exact (one_mul _).symm


/-- The retained literal I closed by a native X edge is a real nullary zero
component. Its vertices/edges remain charged in every ordinary substitution. -/
theorem realizesZeroScalar (hI : RetainsIdentity F) :
    Gadget.Realizes F .disequality (0 : Signature L 0) := by
  have hh := realizes_contract_exact_of_identity (n:=0) F hI
    OrdinaryNormalization.identitySignature
    (Gadget.realizes_of_mem F .disequality OrdinaryNormalization.identitySignature hI)
  have he : Signature.contract Signature.disequality
      (OrdinaryNormalization.identitySignature (K:=L)) = (0 : Signature L 0) := by
    funext x
    norm_num [Signature.contract,OrdinaryNormalization.identitySignature,
      Signature.equality,Signature.disequality]
  rwa [he] at hh

/-- Zero of this boundary arity is an actual disjoint network: the supplied
actual n-port graph tensored with the real nullary zero component. -/
def zeroFrom (hI : RetainsIdentity F) (hf : Gadget.Realizes F .disequality f) :
    DeckDirect F (0 : Signature L n) := by
  have hh := realizes_tensor F .disequality f (0 : Signature L 0) hf (realizesZeroScalar hI)
  have he : Signature.tensor f (0 : Signature L 0) = (0 : Signature L n) := by
    funext x
    simp [Signature.tensor_apply]
  rw [he] at hh
  exact ofRealizes hI hh

end DeckDirect


/-- A data-valued flattened split constructed from the actual saved tree.
Its ports and unit are recursively composed from the stored constructors. -/
inductive SavedSplit {L : Type} [Field L] (r u : AnySignature L) : Type
  | root (equation : r = u)
  | factor (complement : AnySignature L) (split : ProperSplit r u complement)

def savedSlotSplit {L : Type} [Field L] {r : AnySignature L} (t : FactorTree r) :
    (j : FactorSaturation.Slots t) → SavedSplit r (FactorSaturation.slot t j).1 :=
  match t with
  | .leaf _ _ => fun _ => .root rfl
  | .split sp l rr => fun j => match j with
    | .inl _ => .root rfl
    | .inr (.inl j) =>
      match savedSlotSplit l j with
      | .root he => .factor _ (he ▸ sp)
      | .factor b q => .factor _ (sp.composeLeft q)
    | .inr (.inr j) =>
      match savedSlotSplit rr j with
      | .root he => .factor _ (he ▸ sp.swap)
      | .factor b q => .factor _ (sp.swap.composeLeft q)

def savedRootSlot {L : Type} [Field L] {r : AnySignature L} (t : FactorTree r) :
    FactorSaturation.Slots t := match t with
  | .leaf _ _ => ()
  | .split _ _ _ => Sum.inl ()

@[simp] theorem savedRootSlot_value {L : Type} [Field L] {r : AnySignature L} (t : FactorTree r) :
    FactorSaturation.slot t (savedRootSlot t) = (⟨r,t⟩ : TreeOccurrence L) := by
  cases t <;> rfl

theorem savedSlot_cover {L : Type} [Field L] {u t : TreeOccurrence L}
    (h : Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule.StoredSubtree u t) :
    ∃ j : FactorSaturation.Slots t.2, FactorSaturation.slot t.2 j = u := by
  induction h with
  | root t => exact ⟨savedRootSlot t.2,savedRootSlot_value t.2⟩
  | left sp l r h ih =>
      obtain ⟨j,hj⟩ := ih
      exact ⟨.inr (.inl j),hj⟩
  | right sp l r h ih =>
      obtain ⟨j,hj⟩ := ih
      exact ⟨.inr (.inr j),hj⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2
