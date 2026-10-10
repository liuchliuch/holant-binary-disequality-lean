import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryMacro
import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryPinOrDEQ
import Holant.Proofs.Hardness.GeneralEOPinEliminationCases
import Holant.Proofs.Hardness.GeneralEONonARSPinningFieldBridge

/-! A structural actual pin-or-DEQ supplier becomes an implemented unbounded
pin-elimination programme in the family's unchanged generated field. The
nonzero scale is an actual network coefficient, transported through the proved
original-field lift. No ambient scale is assumed to belong to that field and
no field presentation is identified with a separately generated presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryPinning
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution UniversalPairReduction
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue)
end O
namespace B
export GeneralEONonARSPinningFieldBridge (original lift labels exact native denote_lift)
end B
namespace M
export GeneralOddHigherResidueQuaternaryMacro
  (G g arity signatures old_signature new_signature remove source_value_eq deqSource)
end M
namespace E
export GeneralEOCentralHoleHardnessPinning (samePalette sameRows template_arity)
end E
namespace P
export GeneralEOPinnedDescentPalette (pinned)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
abbrev presentation := O.originalPresentation G
abbrev tables := O.originalTables G
abbrev Elimination := GeneralEOPinEliminationCases.Elimination G
abbrev family := Set.range (fun i : Fin s => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))

section Lift
variable {n : ℕ} (N : Network AlgebraicComplex n) (hU : Uses N (family G))

def labels : Labelling N.shape s 1 a where
  vertex v := Classical.choose (hU v)
  vertex_arity v := congrArg Sigma.fst (Classical.choose_spec (hU v))
  edge _ := 0

theorem labels_exact : LabelledNetwork.Exact G N (labels G N hU) :=
  fun v => Classical.choose_spec (hU v)

variable (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀e,N.edge e=Signature.disequality)

theorem lifted_labels : LabelledNetwork.Exact (M.G (presentation G) (tables G))
    (B.lift G N NL) (B.labels G N NL) := by
  change LabelledNetwork.Exact (ValueJoins.signatures (presentation G) (tables G)) _ _
  rw [GeneralEOSinglePinSource.decoded_original]
  exact B.exact G N NL

def scale (x : Fin n → Bool) : O.originalField G := (B.lift G N NL).denote x

include hN hn in
theorem scale_ambient (x : Fin n → Bool) :
    (scale G N NL x : AlgebraicComplex)=N.denote x := B.denote_lift G N NL hN hn x

include hN hn in
private theorem scale_nonzero (x : Fin n → Bool) (hc : N.denote x≠0) : scale G N NL x≠0 := by
  intro hz
  apply hc
  rw [←scale_ambient G N NL hN hn x,hz]
  rfl

end Lift

section Pin
variable (N : Network AlgebraicComplex 2) (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀e,N.edge e=Signature.disequality)
variable (c : AlgebraicComplex) (hc : c≠0)
variable (hv : N.denote=c • GeneralEOPinnedDescentNetwork.directed01)

abbrev pinScale := scale G N NL ![false,true]

include hN hn hv in
theorem pin_scale_ambient : (pinScale G N NL : AlgebraicComplex)=c := by
  rw [pinScale,scale_ambient G N NL hN hn,hv]
  simp [GeneralEOPinnedDescentNetwork.directed01]

include hN hn c hc hv in
theorem pin_scale_nonzero : pinScale G N NL≠0 := by
  apply scale_nonzero G N NL hN hn
  rw [hv]
  simpa [GeneralEOPinnedDescentNetwork.directed01] using hc

include hN hn c hv in
theorem pin_lifted : (B.lift G N NL).denote=
    pinScale G N NL • GeneralEOPinnedDescentNetwork.directed01 := by
  funext x
  apply Subtype.ext
  change ((B.lift G N NL).denote x : AlgebraicComplex)=
    (pinScale G N NL : AlgebraicComplex)*
      ((GeneralEOPinnedDescentNetwork.directed01 x : O.originalField G) : AlgebraicComplex)
  rw [B.denote_lift G N NL hN hn,pin_scale_ambient G N NL hN hn c hv,hv]
  change c*GeneralEOPinnedDescentNetwork.directed01 x=_
  congr 1
  simp only [GeneralEOPinnedDescentNetwork.directed01]
  split_ifs <;> rfl

def pinElimination : Elimination G := by
  let Q := B.lift G N NL
  let QL := B.labels G N NL
  let z := pinScale G N NL
  have hz := pin_scale_nonzero G N NL hN hn c hc hv
  have old := M.old_signature (presentation G) (tables G) Q QL z
  have new := M.new_signature (presentation G) (tables G) Q QL z
    (GeneralEOSinglePinSource.native_tables G) (lifted_labels G N NL) (B.native G N NL)
    hz GeneralEOPinnedDescentNetwork.directed01 (pin_lifted G N NL hN hn c hv)
  simp only [M.G,GeneralEOSinglePinSource.decoded_original] at old
  apply E.samePalette G (M.signatures (presentation G) (tables G) Q QL z)
    (E.template_arity (M.g Q QL) rfl)
    (E.sameRows G _ old new)
  have r := M.remove (presentation G) (tables G) Q QL z hz
  rw [M.source_value_eq (presentation G) (tables G) Q QL z
    (GeneralEOSinglePinSource.native_tables G)] at r
  exact r
end Pin

section DEQ
variable (N : Network AlgebraicComplex 4) (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀e,N.edge e=Signature.disequality)
variable (c : AlgebraicComplex) (hc : c≠0) (hv : N.denote=c • ExactTwoSignatures.E)

abbrev deqScale := scale G N NL ![false,true,false,true]

include hN hn hv in
theorem deq_scale_ambient : (deqScale G N NL : AlgebraicComplex)=c := by
  rw [deqScale,scale_ambient G N NL hN hn,hv]
  simp [ExactTwoSignatures.E_reference]

include hN hn c hc hv in
theorem deq_scale_nonzero : deqScale G N NL≠0 := by
  apply scale_nonzero G N NL hN hn
  rw [hv]
  simpa [ExactTwoSignatures.E_reference] using hc

include hN hn c hv in
theorem deq_lifted : (B.lift G N NL).denote=deqScale G N NL • ExactTwoSignatures.E := by
  funext x
  apply Subtype.ext
  change ((B.lift G N NL).denote x : AlgebraicComplex)=
    (deqScale G N NL : AlgebraicComplex)*((ExactTwoSignatures.E x : O.originalField G) : AlgebraicComplex)
  rw [B.denote_lift G N NL hN hn,deq_scale_ambient G N NL hN hn c hv,hv]
  change c*ExactTwoSignatures.E x=_
  congr 1
  simp only [ExactTwoSignatures.E_reference]
  split_ifs <;> rfl

theorem literal_source_value :
    GeneralEOSinglePinAmplificationProgramme.sourceValue (presentation G) (tables G)=
      GeneralEOSinglePinAmplificationSemantics.value (B.original G) := by
  unfold GeneralEOSinglePinAmplificationProgramme.sourceValue
  change GeneralEOSinglePinAmplificationSemantics.value
    (ValueJoins.signatures (presentation G) (tables G))=_
  rw [GeneralEOSinglePinSource.decoded_original]

def deqElimination : Elimination G := by
  have r := M.deqSource (presentation G) (tables G) (deqScale G N NL)
    (GeneralEOSinglePinSource.native_tables G) (B.lift G N NL) (B.labels G N NL)
    (lifted_labels G N NL) (B.native G N NL) (deq_scale_nonzero G N NL hN hn c hc hv)
    (deq_lifted G N NL hN hn c hv)
  rw [literal_source_value] at r
  apply E.samePalette G (P.pinned G) rfl (fun _ => rfl)
  rw [GeneralEOSinglePinPaletteBridge.literal_family]
  exact r
end DEQ

/-- A proved actual graph alternative is consumed by choosing its finite
supplier once for the fixed family and installing its real scalar programme. -/
def fromPinOrDEQ (h : GeneralOddHigherResidueQuaternaryPinOrDEQ.PinOrDEQ (family G)) :
    Elimination G := by
  classical
  by_cases hp : ∃ P : Network AlgebraicComplex 2,Uses P (family G) ∧ Native P ∧
      ∃ c : AlgebraicComplex,c≠0 ∧ P.denote=c • GeneralEOPinnedDescentNetwork.directed01
  · let N := Classical.choose hp
    have hs := Classical.choose_spec hp
    let c := Classical.choose hs.2.2
    have hc := Classical.choose_spec hs.2.2
    exact pinElimination G N (labels G N hs.1) (labels_exact G N hs.1) hs.2.1 c hc.1 hc.2
  · have hq := h.resolve_left hp
    let N := Classical.choose hq
    have hs := Classical.choose_spec hq
    let c := Classical.choose hs.2.2
    have hc := Classical.choose_spec hs.2.2
    exact deqElimination G N (labels G N hs.1) (labels_exact G N hs.1) hs.2.1 c hc.1 hc.2

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryPinning
