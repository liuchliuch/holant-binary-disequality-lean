import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeMacroAccess
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeComplementSign
import Holant.Proofs.Reductions.GeneralExtraction.RecursiveMachine
import Holant.Proofs.Algorithms.RawArityTransport

/-! A genuine no-I unary factor programme from a literal nonzero pin pair
and a retained two-sided endpoint. The complete general power-exposure and
residue machine handles arbitrary pin counts, including dead residue classes.
Every old row remains literal in the same fixed field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgePinFactor
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction
open GeneralPowerExposure
namespace S
export NativeAntiTargetSource (base)
end S
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace R
export RawArityTransport (input signatures computes denote)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

def pin (b : Bool) : Signature K 1 := fun x=>if x 0=b then 1 else 0

theorem pair : Signature.tensor (pin (K:=K) false) (pin true)=C.antiTensor 1 0 := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [pin,Signature.tensor_apply,C.antiTensor,h0,h1]

def arity (i : ℕ) := if i<s then a i else 1
theorem arity_old (i : Fin s) : a i.val=arity (s:=s) (a:=a) i.val := by simp [arity,i.isLt]
theorem arity_new : arity (s:=s) (a:=a) s=1 := by simp [arity]
def table : (i : Fin s)→Signature K (arity (s:=s) (a:=a) i.val) := R.signatures arity_old H

private theorem cast_literal {m n : ℕ} (f : Signature K m) (h : m=n) :
    (⟨n,fun x=>f (fun j=>x (Fin.cast h j))⟩ : AnySignature K)=⟨m,f⟩ := by
  cases h
  rfl

theorem table_literal (i : Fin s) :
    (⟨arity i.val,table H i⟩ : AnySignature K)=⟨a i.val,H i⟩ := cast_literal (H i) (arity_old i)

theorem table_value (r : ExactSignatureTables.Input s 1 (arity (s:=s) (a:=a))) :
    (S.base (table H) F).evaluate F r=
      (S.base H F).evaluate F (R.input (fun i=>(arity_old i).symm) r) := by
  rw [PaperTerminalBridgeMacroAccess.value,PaperTerminalBridgeMacroAccess.value]
  exact R.denote arity_old H (fun _ : Fin 1=>Signature.disequality)
    (R.input (fun i=>(arity_old i).symm) r)

def table_source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 (arity (s:=s) (a:=a))) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((S.base (table H) F).evaluate F) ((S.base H F).evaluate F) :=
  controlledOneQueryOfEq (R.computes (fun i=>(arity_old i).symm)) (identityComputes F.encoding)
    ((S.base H F).outputBound F) ((S.base (table H) F).evaluate F) (table_value H F)

theorem mixed (q : Signature K 4) (j : Fin s)
    (literal : (⟨a j.val,H j⟩ : AnySignature K)=⟨4,q⟩)
    (first : (entries q).a≠0) (last : (entries q).x≠0) :
    GeneralCarrierExistence.MixedSupport
      (Set.range (fun i=>(⟨arity i.val,table H i⟩ : AnySignature K))) := by
  intro bit
  refine ⟨4,q,⟨j,(table_literal H j).trans literal⟩,(fun _=>bit),?_,?_⟩
  · have word (b : Bool) : (fun _ : Fin 4=>b)=![b,b,b,b] := by
      funext i
      fin_cases i <;> rfl
    rw [word]
    cases bit
    · exact first
    · exact last
  · simp [Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.balance]

def factor : Signature K (arity (s:=s) (a:=a) s) :=
  fun x=>pin false (fun j=>x (Fin.cast arity_new.symm j))

theorem factor_literal : (⟨arity (s:=s) (a:=a) s,factor (K:=K) (s:=s) (a:=a)⟩ : AnySignature K)=
    ⟨1,pin false⟩ := cast_literal (pin false) arity_new.symm

variable (q : Signature K 4) (j k : Fin s)
variable (literalQ : (⟨a j.val,H j⟩ : AnySignature K)=⟨4,q⟩)
variable (first : (entries q).a≠0) (last : (entries q).x≠0)
variable (literalPair : (⟨a k.val,H k⟩ : AnySignature K)=⟨2,C.antiTensor 1 0⟩)

private def cast_power {m n : ℕ} {f : Signature K m} {g : Signature K n}
    (h : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (P : PowerMacro H f) : PowerMacro H g := by
  cases h
  exact P

def power : PowerMacro (table H) (factor (K:=K) (s:=s) (a:=a)) := by
  classical
  have pairmem : (⟨1+1,Signature.tensor (pin (K:=K) false) (pin true)⟩ : AnySignature K)∈
      Set.range (fun i=>(⟨arity i.val,table H i⟩ : AnySignature K)) := by
    refine ⟨k,?_⟩
    rw [pair]
    exact (table_literal H k).trans literalPair
  have nonzero : pin (K:=K) true≠0 := by
    intro zero
    have h := congrFun zero ![true]
    simp [pin] at h
  have p := Classical.choice (labelled_power (table H) (by norm_num)
    (mixed H q j literalQ first last) (pin false) (pin true) (by norm_num) nonzero pairmem)
  exact cast_power (table H) factor_literal.symm p

def extended := RetainedPairReduction.extended (table H) (factor (K:=K) (s:=s) (a:=a))

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1 (arity (s:=s) (a:=a))) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((S.base (extended H) F).evaluate F) ((S.base H F).evaluate F) :=
  Programme.compose (RecursiveMachine.step F (factor (K:=K) (s:=s) (a:=a))
    (power H q j k literalQ first last literalPair)) (table_source H F)

theorem old_literal (i : Fin s) :
    (⟨arity (Fin.castAdd 1 i).val,extended H (Fin.castAdd 1 i)⟩ : AnySignature K)=⟨a i.val,H i⟩ := by
  have value := GeneralOriginalQuery.source_old (table H) (factor (K:=K) (s:=s) (a:=a)) i
  exact (congrArg (fun f : Signature K (arity i.val)=>(⟨arity i.val,f⟩ : AnySignature K)) value).trans
    (table_literal H i)

theorem new_literal :
    (⟨arity s,extended H ⟨s,Nat.lt_succ_self _⟩⟩ : AnySignature K)=⟨1,pin false⟩ := by
  rw [extended,RetainedPairReduction.extended,GeneralOriginalQuery.source_new]
  exact factor_literal

#check power

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgePinFactor
end
