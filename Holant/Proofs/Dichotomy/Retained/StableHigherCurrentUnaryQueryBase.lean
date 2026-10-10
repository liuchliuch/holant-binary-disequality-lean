import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentUnaryQueryTrace

/-! Repaired actual-query control for the original-L pure-pin source.
This separate leaf preserves the failed original source and its diagnostics.
The old accessOriginalL and its existentially chosen Poly reduction are untouched.
V2 selects actual dichotomy NETWORK data, then installs the existing literal
one- or three-query program with an actual-prefix byte certificate. The original
two power macros, factor chain, ports, tables and field conversions are reused.
Fixed-family noncomputable installation is explicit; no uniform recognition-time
claim or Poly-to-LengthControlled coercion is made.
-/
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentUnaryQueryControl
open Holant Holant.Tractable Holant.Algebraic Turing Computability
open Holant.Complexity BinaryCompose FixedFieldMachines OracleBatch StackProtocol
open Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open UniversalPairReduction FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain

namespace Base
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {n s : ℕ} {arity : ℕ → ℕ}

def transfer {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {eq : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}
    (r : LengthControlledOracleReduction ea eb eq ed f g) (h : α → β)
    (he : ∀x,h x=f x) : LengthControlledOracleReduction ea eb eq ed h g where
  reduction := SmoothingCompiler.sourceTransfer r.reduction h he
  targetOutput := r.targetOutput
  queryBound := r.queryBound
  safeQuery := r.safeQuery

def Symmetric (G : (i : Fin s) → Signature K (arity i.val)) : Prop :=
  ∀f : Signature K 2, Gadget.Realizes (BinaryFamily.family G) .disequality f →
    f ![false,true]=f ![true,false]

/-- Only original physical witness data are selected. A reduction machine is
then constructed explicitly by the following factory; it is never selected
from an existential Poly/AtMostQueries specification. -/
inductive Branch (G : (i : Fin s) → Signature K (arity i.val)) : Type
  | symmetric (hs : Symmetric G)
  | asymmetric (W : Network K 2)
      (hW : ∀v,(⟨W.shape.arity v,W.vertex v⟩ : AnySignature K)∈BinaryFamily.family G)
      (hE : ∀e,W.edge e=Signature.disequality)
      (ha : W.denote ![false,true]≠W.denote ![true,false])

def branch (G : (i : Fin s) → Signature K (arity i.val)) : Branch G := by
  classical
  exact if hs : Symmetric G then .symmetric hs else
    let existsNetwork := (actual_binary_dichotomy (BinaryFamily.family G)).resolve_left hs
    let W := Classical.choose existsNetwork
    let facts := Classical.choose_spec existsNetwork
    .asymmetric W facts.1 facts.2.1 facts.2.2

variable (F : FixedField K n) (T : ExactSignatureTables n s 1 arity)

def symmetric : LengthControlledOracleReduction (inputEncoding s arity) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    (SmoothingCompiler.symmetricReducedValue F T) (T.evaluate F) :=
  ControlledCap.controlledContext (SmoothingCompiler.queryWithFlagsComputes s arity)
    (SmoothingCompiler.symmetricPostComputes F) (T.outputBound F)

def asymmetric {S : NetworkShape 2} (lab : Labelling S s 1 arity) (b c : K) :
    LengthControlledOracleReduction (inputEncoding s arity) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      (SmoothingCompiler.asymmetricReducedValue F T lab b c) (T.evaluate F) :=
  ThreeTrace.controlled (SmoothingCompiler.preparedComputes lab)
    (SmoothingCompiler.asymmetricPostComputes F b c) (T.outputBound F)

@[simp] theorem symmetric_reduction :
    (symmetric F T).reduction=SmoothingCompiler.symmetricReduction F T := rfl
@[simp] theorem asymmetric_reduction {S : NetworkShape 2} (lab : Labelling S s 1 arity) (b c : K) :
    (asymmetric F T lab b c).reduction=SmoothingCompiler.asymmetricReduction F T lab b c := rfl

theorem symmetric_origin (oracle : List Bool → List Bool) (r : Input s arity) (t : ℕ)
    (cfg : (symmetric F T).reduction.machine.Cfg)
    (hr : (symmetric F T).reduction.machine.run oracle ((inputEncoding s arity).encode r) t=some cfg)
    (hq : (symmetric F T).reduction.machine.IsQuery cfg) :
    cfg=ContextControl.queryCfg (SmoothingCompiler.queryWithFlagsComputes s arity).machine
      (SmoothingCompiler.symmetricPostComputes F).machine
      ((RawClosedNetwork.validatedEncoding s 1 arity).encode (Surgery.query r))
      (SmoothingCompiler.flagsEncoding.encode (SmoothingCompiler.flags r)) :=
  ContextControl.query_configuration _ _ oracle _ _ _
    ((SmoothingCompiler.queryWithFlagsComputes s arity).outputs r).steps t cfg
    ((SmoothingCompiler.queryWithFlagsComputes s arity).outputs r).evals_in_steps hr hq

/-- The original native surgery, plus witness, and port-reversed minus witness
are the ONLY three query words at the actual asymmetric caller prefixes. -/
theorem asymmetric_origin {S : NetworkShape 2} (lab : Labelling S s 1 arity) (b c : K)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding (T.evaluate F) oracle)
    (r : Input s arity) (t : ℕ) (cfg : (asymmetric F T lab b c).reduction.machine.Cfg)
    (hr : (asymmetric F T lab b c).reduction.machine.run oracle ((inputEncoding s arity).encode r) t=some cfg)
    (hq : (asymmetric F T lab b c).reduction.machine.IsQuery cfg) :
    cfg.stk (asymmetric F T lab b c).reduction.machine.queryStack=
      (RawClosedNetwork.validatedEncoding s 1 arity).encode (Surgery.query r) ∨
    cfg.stk (asymmetric F T lab b c).reduction.machine.queryStack=
      (RawClosedNetwork.validatedEncoding s 1 arity).encode (OrderedQueries.plus lab (forget s arity r)) ∨
    cfg.stk (asymmetric F T lab b c).reduction.machine.queryStack=
      (RawClosedNetwork.validatedEncoding s 1 arity).encode (OrderedQueries.minus lab (forget s arity r)) := by
  simpa only [asymmetric,ThreeTrace.controlled,SmoothingCompiler.targetEncoding,
    SmoothingCompiler.prepared] using
    ThreeTrace.query_origin (SmoothingCompiler.preparedComputes lab)
      (SmoothingCompiler.asymmetricPostComputes F b c) (T.outputBound F) oracle ho r t cfg hr hq

/-- Both exhaustive physical branches retain original native-X tables and
literal query compilers. Branch selection is offline for this fixed family. -/
def source (hnative : ∀i a b,F.decode (T.edge i a b)=Signature.disequality a b) :
    LengthControlledOracleReduction (inputEncoding s arity) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      (BinaryFamily.value (ValueJoins.signatures F T) BinaryTable.delta) (T.evaluate F) :=
  match branch (ValueJoins.signatures F T) with
  | .symmetric hs => transfer (symmetric F T)
      (BinaryFamily.value (ValueJoins.signatures F T) BinaryTable.delta)
      (ValueJoins.symmetric_exact F T hnative hs)
  | .asymmetric W hW hE ha =>
      let lab := FiniteFamily.labelling (ValueJoins.signatures F T) W hW
      have hLab : lab.sourceNetwork (ValueJoins.signatures F T) (fun _ : Fin 1 => Signature.disequality)=W :=
        FiniteFamily.labelled_network (ValueJoins.signatures F T) W hW hE
      have hGap : QueryFamily.binary (ValueJoins.signatures F T) lab (Equiv.refl _) false true ≠
          QueryFamily.binary (ValueJoins.signatures F T) lab (Equiv.refl _) true false := by
        simpa only [QueryFamily.binary_plus,hLab] using ha
      transfer (asymmetric F T lab
        (QueryFamily.binary (ValueJoins.signatures F T) lab (Equiv.refl _) false true)
        (QueryFamily.binary (ValueJoins.signatures F T) lab (Equiv.refl _) true false))
        (BinaryFamily.value (ValueJoins.signatures F T) BinaryTable.delta)
        (ValueJoins.asymmetric_exact F T hnative lab hGap)

end Base

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentUnaryQueryControl
