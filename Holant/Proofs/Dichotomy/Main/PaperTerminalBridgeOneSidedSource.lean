import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseSource
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgePinNetwork
import Holant.Proofs.Dichotomy.Native.NativeNormalizedGraphAdjoin

/-! Complete native one-sided antidiagonal continuation. The semantic output
is normalized by an actual labelled macro, its unary factor is exposed by
the general no-I power programme, and two pins yield a literal nonsingular
weighted equality. The original field and every old row are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeOneSidedSource
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export NativeAntiTargetSource (base)
export PaperTerminalBridgeDenseSemantic (family)
end S
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (binarySignature)
export GeneralCancellationCapPin (antiTensor)
end C
namespace A
export PaperTerminalBridgeAntiGroup (Available)
export NativeNormalizedGraphAdjoin (arity signatures old old_literal newLabel normalized_literal source)
end A
namespace P
export PaperTerminalBridgePinFactor (pin extended source old_literal new_literal)
end P
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

theorem zero_available (oneSided : PaperTerminalBridgeDenseSource.OneSided (S.family H)) :
    A.Available (S.family H) 0 := by
  obtain ⟨p,q,actual,h | h⟩ := oneSided
  · have reversed := PaperTerminalBridgeEqualProductsCaps.symm (S.family H) p q actual
    have ratio := PaperTerminalBridgeFiniteDeck.ratio_actual (S.family H) q p h.2 reversed
    simpa [h.1] using ratio
  · have ratio := PaperTerminalBridgeFiniteDeck.ratio_actual (S.family H) p q h.1 actual
    simpa [h.2] using ratio

structure Extension where
  count : ℕ
  b : ℕ→ℕ
  table : (i : Fin count)→Signature K (b i.val)
  old : Fin s→Fin count
  old_literal : ∀i,(⟨b (old i).val,table (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩
  label : Fin count
  p : K
  q : K
  p_nonzero : p≠0
  q_nonzero : q≠0
  literal : (⟨b label.val,table label⟩ : AnySignature K)=⟨2,C.binarySignature (D.diagonal p q)⟩
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((S.base table F).evaluate F) ((S.base H F).evaluate F)

variable (q : Signature K 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,q⟩)
variable (even : EvenSupport q) (dense : StableDenseParityAlgebra.Dense q)
variable (oneSided : PaperTerminalBridgeDenseSource.OneSided (S.family H))

include literal even dense oneSided in
theorem extension_exists : Nonempty (Extension H F) := by
  classical
  obtain ⟨c,hc,N,form⟩ := PaperTerminalBridgeDenseSemantic.output H 0 (zero_available H oneSided) zero_ne_one
  have normalized : N.network.denote=fun x=>c*C.antiTensor 1 0 x := by
    rw [form,PaperTerminalBridgeDenseSemantic.anti_eq]
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [C.antiTensor,h0,h1]
  let J := A.signatures F H N c
  let j := A.old H label
  let k := A.newLabel H
  have jq : (⟨A.arity H N j.val,J j⟩ : AnySignature K)=⟨4,q⟩ :=
    (A.old_literal F H N c label).trans literal
  have kp : (⟨A.arity H N k.val,J k⟩ : AnySignature K)=⟨2,C.antiTensor 1 0⟩ :=
    A.normalized_literal F H N c _ hc normalized
  let J2 := P.extended J
  let j2 : Fin (s+2) := Fin.castAdd 1 j
  let k2 : Fin (s+2) := ⟨s+1,by omega⟩
  have jq2 : (⟨PaperTerminalBridgePinFactor.arity j2.val,J2 j2⟩ : AnySignature K)=⟨4,q⟩ :=
    (P.old_literal J j).trans jq
  have kp2 : (⟨PaperTerminalBridgePinFactor.arity k2.val,J2 k2⟩ : AnySignature K)=⟨1,P.pin false⟩ :=
    P.new_literal J
  let W := PaperTerminalBridgePinNetwork.output J2 q j2 k2 jq2 kp2
  have fw : W.network.denote=fun x=>1*C.binarySignature (D.diagonal (entries q).y (entries q).x) x := by
    change (PaperTerminalBridgePinNetwork.network q).denote=_
    simpa only [one_mul] using PaperTerminalBridgePinNetwork.value q even
  let J3 := A.signatures F J2 W 1
  refine ⟨{
    count:=s+3
    b:=A.arity J2 W
    table:=J3
    old:=fun i=>A.old J2 (Fin.castAdd 1 (A.old H i))
    old_literal:=?_
    label:=A.newLabel J2
    p:=(entries q).y
    q:=(entries q).x
    p_nonzero:=dense.2.2.2.2.2.2.1
    q_nonzero:=dense.2.2.2.2.2.2.2
    literal:=A.normalized_literal F J2 W 1 _ one_ne_zero fw
    source:=Programme.compose (A.source F J2 W 1 one_ne_zero)
      (Programme.compose (P.source J F q j k jq dense.1 dense.2.2.2.2.2.2.2 kp)
        (A.source F H N c hc)) }⟩
  intro i
  exact (A.old_literal F J2 W 1 (Fin.castAdd 1 (A.old H i))).trans
    ((P.old_literal J (A.old H i)).trans (A.old_literal F H N c i))

def produce : Extension H F := (extension_exists H F q label literal even dense oneSided).some

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeOneSidedSource
end
