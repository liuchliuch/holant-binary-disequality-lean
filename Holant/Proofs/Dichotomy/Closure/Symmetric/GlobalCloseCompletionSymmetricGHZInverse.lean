import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryProjector
import Holant.Complexity.BinaryInterpolation.SpectralForms

/-! Finite-target interpolation adjoins a scalar inverse of any actual
ordinary binary with two distinct nonzero characteristic roots and infinite
root ratio. The chain semantics are derived from the actual matrix; the
old table and fixed-field codec are unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZInverse
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation
open Holant.Complexity.BinaryInterpolation.Chains hiding binarySignature
open Holant.LocalDrafts.BinaryInterpolation Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace X
export NoXOrdinaryGraphAdjoin (Output baseTables template macro_exact)
end X
namespace R
export OrdinaryTargetInterpolationRecovery (G kernels S)
end R
namespace F
export OrdinaryTargetInterpolationFamily (signatures tables old_literal new_literal controlled)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def inversePencil (B : Binary (K:=K)) (a b : K) : Binary (K:=K) :=
  (1-spectralProjector B a b)+(b/a) • spectralProjector B a b

theorem powers (B : Binary (K:=K)) (a b : K) (distinct : a≠b) (hb : b≠0)
    (trace : Matrix.trace B=a+b) (determinant : Matrix.det B=a*b) (k : ℕ) :
    B^k=b^k • ((1-spectralProjector B a b)+(a/b)^k • spectralProjector B a b) := by
  rw [distinct_power B a b distinct trace determinant,smul_add,smul_smul]
  have scalar : b^k*(a/b)^k=a^k := by rw [div_pow]; field_simp
  rw [scalar]
  exact add_comm _ _

theorem inverse_left (B : Binary (K:=K)) (a b : K) (distinct : a≠b) (ha : a≠0)
    (trace : Matrix.trace B=a+b) (determinant : Matrix.det B=a*b) :
    inversePencil B a b*B=b • (1 : Binary (K:=K)) := by
  rw [inversePencil,add_mul,Matrix.smul_mul,complementProjector_mul B a b distinct trace determinant,
    spectralProjector_mul B a b trace determinant,smul_smul]
  have scalar : (b/a)*a=b := div_mul_cancel₀ b ha
  rw [scalar]
  module

theorem inverse_commute (B : Binary (K:=K)) (a b : K) :
    B*inversePencil B a b=inversePencil B a b*B := by
  simp only [inversePencil,spectralProjector,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,
    Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul]

theorem inverse_right (B : Binary (K:=K)) (a b : K) (distinct : a≠b) (ha : a≠0)
    (trace : Matrix.trace B=a+b) (determinant : Matrix.det B=a*b) :
    B*inversePencil B a b=b • (1 : Binary (K:=K)) := by
  rw [inverse_commute,inverse_left B a b distinct ha trace determinant]

section Source
variable [Algebra ℚ K] {r degree : ℕ} {arity : ℕ→ℕ}
variable (field : FixedField K degree) (H : (i : Fin r)→Signature K (arity i.val))
variable (N : X.Output H 2) (a b : K)
abbrev matrix := binaryMatrix N.network.denote
abbrev base := X.baseTables field H
abbrev template := X.template H N
def data : OrdinaryTargetInterpolationMachine.Data field (base field H) where
  template := template H N
  valid := N.labels.wellFormed
  binary := rfl
  edge := 0
  gamma := b
  rho := a/b
  target := b/a
abbrev left := 1-spectralProjector (matrix H N) a b
abbrev right := spectralProjector (matrix H N) a b
abbrev outputArity := OrdinaryTargetInterpolationFamily.a (data field H N a b)
abbrev signatures := F.signatures (data field H N a b) (left H N a b) (right H N a b)
abbrev tables := F.tables (data field H N a b) (left H N a b) (right H N a b)

variable (distinct : a≠b) (ha : a≠0) (hb : b≠0)
variable (trace : Matrix.trace (matrix H N)=a+b) (determinant : Matrix.det (matrix H N)=a*b)

include distinct hb trace determinant in
theorem chain (k : ℕ) :
    ((explicitTemplate r 0 k).network
      (explicitTemplate_wellFormed (PhysicalQueries.A (s:=r) arity (template H N)) PhysicalQueries.newLabel
        (PhysicalQueries.new_arity (s:=r) arity (template H N) rfl) (0 : Fin 1) k)
      (R.S (data field H N a b))
      (R.kernels (field:=field) (T:=base field H))).denote=
      binarySignature (b^(k+1) • (left H N a b+(a/b)^(k+1) • right H N a b)) := by
  have macroValue : (⟨(template H N).boundary,((template H N).network N.labels.wellFormed
      (R.G (field:=field) (T:=base field H)) (R.kernels (field:=field) (T:=base field H))).denote⟩ : AnySignature K)=
      ⟨2,binarySignature (matrix H N)⟩ := by
    apply congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K))
    exact (X.macro_exact field H N).trans (binarySignature_binaryMatrix _).symm
  have h:=OrdinaryTargetInterpolationChain.explicitTemplate_denote_I
    (PhysicalQueries.A (s:=r) arity (template H N)) PhysicalQueries.newLabel
    (PhysicalQueries.new_arity (s:=r) arity (template H N) rfl) (0 : Fin 1) k (matrix H N)
    (OriginalTables.tables (template H N) N.labels.wellFormed
      (R.G (field:=field) (T:=base field H)) (R.kernels (field:=field) (T:=base field H)))
    (R.kernels (field:=field) (T:=base field H))
    ((OriginalTables.tables_new (template H N) N.labels.wellFormed
      (R.G (field:=field) (T:=base field H)) (R.kernels (field:=field) (T:=base field H))).trans macroValue)
    (by funext p q;exact field.decode.apply_symm_apply (Signature.equality p q))
  exact h.trans (congrArg binarySignature (powers (matrix H N) a b distinct hb trace determinant (k+1)))

theorem old_literal (i : Fin r) :
    (⟨outputArity field H N a b (Fin.castAdd 1 i).val,signatures field H N a b (Fin.castAdd 1 i)⟩ : AnySignature K)=
      ⟨arity i.val,H i⟩ := by
  have h:=F.old_literal (data field H N a b) (left H N a b) (right H N a b) i
  refine h.trans ?_
  apply congrArg (fun f : Signature K (arity i.val)=>(⟨arity i.val,f⟩ : AnySignature K))
  funext x
  exact field.decode.apply_symm_apply (H i x)

theorem new_literal :
    (⟨outputArity field H N a b r,signatures field H N a b ⟨r,Nat.lt_succ_self _⟩⟩ : AnySignature K)=
      ⟨2,binarySignature (inversePencil (matrix H N) a b)⟩ :=
  F.new_literal (data field H N a b) (left H N a b) (right H N a b)

def controlled (infinite : ∀k : ℕ,0<k→(a/b)^k≠1) : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+1) 1 (outputArity field H N a b)) field.encoding
    (RawClosedNetwork.validatedEncoding r 1 arity) field.encoding
    ((QuaternaryOrdinaryCompanion.tables field (signatures field H N a b)).evaluate field)
    ((base field H).evaluate field) :=
  F.controlled (data field H N a b) (left H N a b) (right H N a b)
    (chain field H N a b distinct hb trace determinant) hb
    (OrdinaryNegativeBinaryUnsignedInterpolationFormulas.nodes_injective (a/b) (div_ne_zero ha hb) infinite)


end Source
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZInverse
end
