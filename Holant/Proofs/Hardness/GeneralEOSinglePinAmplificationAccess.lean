import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationSemantics
import Holant.Proofs.Algorithms.MacroTransport

/-! The anchored reference compiler is a same-field controlled one-query
reduction from unbounded literal directed pins to exactly one directed pin. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationAccess
open Computability Holant Holant.Complexity Holant.Algebraic
open BinaryCompose UniversalPairReduction
namespace S
export GeneralEOSinglePinAmplificationSemantics (value query query_value)
end S
namespace A
export GeneralEOSinglePinAmplificationCompiler (Input inputEncoding queryComputes)
end A
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (a i.val))

def tables : ExactSignatureTables d (s+1) 1 (extendedArity s a) where
  vertex i x := F.decode.symm (BinaryFamily.signatures G BinaryTable.delta i x)
  edge _ b c := F.decode.symm (Signature.disequality b c)

theorem tables_value (r : A.Input (s:=s) (a:=a)) : (tables F G).evaluate F r=S.value G r := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [tables,LinearEquiv.apply_symm_apply]
  rfl

def onePinOutput : PolynomialOutputBound (UniversalPairReduction.inputEncoding s a) F.encoding
    (BinaryFamily.value G BinaryTable.delta) where
  bound := ((tables F G).outputBound F).bound
  length_le r := by
    have h := ((tables F G).outputBound F).length_le (forget s a r)
    rw [tables_value] at h
    exact h

variable (j : Fin s)
variable (hE : (⟨a j.val,G j⟩ : AnySignature K)=⟨4,ExactTwoSignatures.E⟩)

/-- The extra oracle is the literal at-most-one-pin partition function;
query correctness is proved by the actual reference graph, not supplied. -/
def source : LengthControlledOracleReduction (A.inputEncoding (s:=s) (a:=a)) F.encoding
    (UniversalPairReduction.inputEncoding s a) F.encoding
    (S.value G) (BinaryFamily.value G BinaryTable.delta) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (A.queryComputes j.isLt (congrArg Sigma.fst hE)) (identityComputes F.encoding)
    (onePinOutput F G) (S.value G) (fun r => (S.query_value G j hE r).symm)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinAmplificationAccess
