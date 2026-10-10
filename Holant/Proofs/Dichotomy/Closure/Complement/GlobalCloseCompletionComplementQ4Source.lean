import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4BatchExecution
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerResult

/-! Actual original-field native-X spectral sources. Every original row is
retained literally. The new support projector or separated Bell row is backed
by the complete polynomial-time chain-query and difference-arithmetic machine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Source
open Holant Holant.Algebraic Holant.Complexity
namespace S
export NativeAntiTargetSource (Output base)
end S
namespace C
export GlobalCloseCompletionComplementQ4ChainCompilerSemantics (arity slot slot_new slot_old)
end C
namespace M
export GlobalCloseCompletionComplementQ4BatchExecution (controlled)
end M
namespace R
export GlobalCloseCompletionComplementQ4ChainCompilerResult (evaluate_base separated support separated_evaluate support_evaluate)
end R
namespace P
export GlobalCloseCompletionComplementQ4Series (ofSpectrum row)
export GlobalCloseCompletionComplementQ4Basis (basis)
export GlobalCloseCompletionComplementQ4Nodes (Separated)
end P
namespace U
export GlobalCloseCompletionComplementQ4SupportBasis (filled support rank_three)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

structure Extension (f : Signature K 4) where
  count : ℕ
  arity : ℕ→ℕ
  table : (i : Fin count)→Signature K (arity i.val)
  old : Fin s→Fin count
  old_literal : ∀i,(⟨arity (old i).val,table (old i)⟩ : AnySignature K)=⟨a i.val,H i⟩
  label : Fin count
  literal : (⟨arity label.val,table label⟩ : AnySignature K)=⟨4,f⟩
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((S.base table F).evaluate F) ((S.base H F).evaluate F)

variable (N : S.Output H 4) (v : Fin 4→K) (form : N.network.denote=P.ofSpectrum v)

/-- Recover all nonzero Bell modes at exponent zero. No multiplicative
separation, supplied identity, or pin resource is required. -/
def support : Extension H F (P.ofSpectrum (U.support v)) := by
  let f:=P.ofSpectrum (U.support v)
  have value : (S.base (C.slot H N f) F).evaluate F=
      GlobalCloseCompletionComplementQ4Batch.result F H N (U.filled v) true 0 := by
    funext x
    exact R.support_evaluate F H N x v form 0
  refine {
    count:=s+1
    arity:=C.arity H N
    table:=C.slot H N f
    old:=Fin.castAdd 1
    old_literal:=C.slot_old H N f
    label:=⟨s,Nat.lt_succ_self _⟩
    literal:=C.slot_new H N f
    source:=?_ }
  rw [value]
  exact M.controlled F H N (U.filled v) true 0

/-- A separated Bell mode is extracted by the same physical machine with
one additional positive sample and the nonzero target denominator. -/
def separated (j : Fin 4) (guard : P.Separated v j) : Extension H F (P.basis j) := by
  have value : (S.base (C.slot H N (P.basis j)) F).evaluate F=
      GlobalCloseCompletionComplementQ4Batch.result F H N v false j := by
    funext x
    exact R.separated_evaluate F H N x v form j guard
  refine {
    count:=s+1
    arity:=C.arity H N
    table:=C.slot H N (P.basis j)
    old:=Fin.castAdd 1
    old_literal:=C.slot_old H N (P.basis j)
    label:=⟨s,Nat.lt_succ_self _⟩
    literal:=C.slot_new H N (P.basis j)
    source:=?_ }
  rw [value]
  exact M.controlled F H N v false j

/-- The redundant rank-three transfer matrix supplies literal full-six EO. -/
def rankThree (h0 : v 0≠0) (h1 : v 1≠0) (h2 : v 2≠0) (h3 : v 3=0) :
    Extension H F (P.row 0 1 ((2:K)⁻¹) ((2:K)⁻¹)) := by
  rw [←U.rank_three v h0 h1 h2 h3]
  exact support H F N v form


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Source
end
