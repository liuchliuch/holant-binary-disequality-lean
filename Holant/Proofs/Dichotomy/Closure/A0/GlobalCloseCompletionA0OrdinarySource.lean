import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0IdentityAdjoin
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion
import Holant.Complexity.EdgeSubdivision.Reduction

/-! Actual ordinary access to the complete Hadamard-normalized current
family. Each ordinary edge is subdivided through the literal identity adjoin
between two signed Z edges. The complete substitution ends at original G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0OrdinarySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionA0Workfield (K field z table table_value)
end W
namespace O
export GlobalCloseCompletionA0IdentityAdjoin
  (arity table tables source literal_arity oldLabel identityLabel old_signature identity_signature)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

abbrev tables := QuaternaryOrdinaryCompanion.tables (W.field G) (W.table G P)
abbrev value := (tables G P).evaluate (W.field G)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding P.count 1 P.arity
abbrev binary := fun (_ : Fin 1) b c => (W.field G).decode.symm (Signature.equality b c)
abbrev wire := fun b c => (W.field G).decode.symm (W.z G b c)
abbrev extendedTables := EdgeSubdivision.targetTables (tables G P) (binary G) (wire G)
abbrev extendedArity := EdgeSubdivision.targetArity P.count P.arity

private def retype {b : ℕ → ℕ} (h : O.arity G P=b) :
    ExactSignatureTables (Module.finrank ℚ (W.K G)) (P.count+1) 1 b := h ▸ O.tables G P

private theorem retype_vertex {b : ℕ → ℕ} (h : O.arity G P=b) (i : Fin (P.count+1)) :
    (⟨b i.val,fun x => (W.field G).decode ((retype G P h).vertex i x)⟩ : AnySignature (W.K G))=
      ⟨O.arity G P i.val,O.table G P i⟩ := by
  cases h
  rfl

private theorem retype_edge {b : ℕ → ℕ} (h : O.arity G P=b) :
    (retype G P h).edge=(O.tables G P).edge := by
  cases h
  rfl

private def retypeSource {b : ℕ → ℕ} (h : O.arity G P=b) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (P.count+1) 1 b) (W.field G).encoding
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
      ((retype G P h).evaluate (W.field G)) (OriginalForestSource.value G) := by
  cases h
  exact O.source G P

private theorem tables_ext {n c d : ℕ} {b : ℕ → ℕ}
    {T U : ExactSignatureTables n c d b} (hv : T.vertex=U.vertex) (he : T.edge=U.edge) : T=U := by
  cases T
  cases U
  cases hv
  cases he
  rfl

private theorem old_extended (i : Fin P.count) :
    (⟨extendedArity G P (Fin.castAdd 1 i).val,
      fun x => (W.field G).decode ((extendedTables G P).vertex (Fin.castAdd 1 i) x)⟩ :
        AnySignature (W.K G))=⟨P.arity i.val,W.table G P i⟩ := by
  have hd := EdgeSubdivision.decode_extended (W.field G) (tables G P) (binary G) (Fin.castAdd 1 i)
  have de : (fun i x => (W.field G).decode ((tables G P).vertex i x))=W.table G P := by
    funext i x
    exact LinearEquiv.apply_symm_apply _ _
  have db : (fun j b c => (W.field G).decode (binary G j b c))=
      (fun _ : Fin 1 => Signature.equality) := by
    funext j b c
    exact LinearEquiv.apply_symm_apply _ _
  simp only [de,db] at hd
  exact (congrArg (fun f : Signature (W.K G) (extendedArity G P (Fin.castAdd 1 i).val) =>
    (⟨extendedArity G P (Fin.castAdd 1 i).val,f⟩ : AnySignature (W.K G))) (funext hd)).trans
      (Sigma.ext (by simp [extendedArity,EdgeSubdivision.targetArity,i.isLt])
        (EdgeSubdivision.extendedSignatures_old_heq (W.table G P)
          (fun _ : Fin 1 => Signature.equality) i))

private theorem new_extended :
    (⟨extendedArity G P (O.identityLabel G P).val,
      fun x => (W.field G).decode ((extendedTables G P).vertex (O.identityLabel G P) x)⟩ :
        AnySignature (W.K G))=⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := by
  have label : O.identityLabel G P=Fin.natAdd P.count (0 : Fin 1) := rfl
  rw [label]
  have hd := EdgeSubdivision.decode_extended (W.field G) (tables G P) (binary G)
    (Fin.natAdd P.count (0 : Fin 1))
  have de : (fun i x => (W.field G).decode ((tables G P).vertex i x))=W.table G P := by
    funext i x
    exact LinearEquiv.apply_symm_apply _ _
  have db : (fun j b c => (W.field G).decode (binary G j b c))=
      (fun _ : Fin 1 => Signature.equality) := by
    funext j b c
    exact LinearEquiv.apply_symm_apply _ _
  simp only [de,db] at hd
  exact (congrArg (fun f : Signature (W.K G) (extendedArity G P P.count) =>
    (⟨extendedArity G P P.count,f⟩ : AnySignature (W.K G))) (funext hd)).trans
      (Sigma.ext (by simp [extendedArity,EdgeSubdivision.targetArity])
        (EdgeSubdivision.extendedSignatures_new_heq (W.table G P)
          (fun _ : Fin 1 => Signature.equality) (0 : Fin 1)))

private theorem extended_tables : retype G P (O.literal_arity G P)=extendedTables G P := by
  apply tables_ext
  · funext i x
    apply (W.field G).decode.injective
    have h : (⟨extendedArity G P i.val,
        fun y => (W.field G).decode ((retype G P (O.literal_arity G P)).vertex i y)⟩ :
          AnySignature (W.K G))=⟨extendedArity G P i.val,
            fun y => (W.field G).decode ((extendedTables G P).vertex i y)⟩ := by
      refine (retype_vertex G P (O.literal_arity G P) i).trans ?_
      by_cases hi : i.val<P.count
      · have label : i=O.oldLabel G P ⟨i.val,hi⟩ := Fin.ext rfl
        rw [label]
        exact (O.old_signature G P ⟨i.val,hi⟩).trans (old_extended G P ⟨i.val,hi⟩).symm
      · have label : i=O.identityLabel G P := Fin.ext (by change i.val=P.count; have := i.isLt; omega)
        rw [label]
        exact (O.identity_signature G P).trans (new_extended G P).symm
    exact congrFun (eq_of_heq (Sigma.mk.inj_iff.mp h).2) x
  · rw [retype_edge]
    rfl

def extendedSource : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (P.count+1) 1 (extendedArity G P)) (W.field G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((extendedTables G P).evaluate (W.field G)) (OriginalForestSource.value G) := by
  have r := retypeSource G P (O.literal_arity G P)
  rw [extended_tables] at r
  exact r

theorem fuse (j : Fin 1) (b c : Bool) :
    (∑uv : Bool×Bool,
      (W.field G).decode (wire G b uv.1) *
      (W.field G).decode (binary G j uv.1 uv.2) *
      (W.field G).decode (wire G uv.2 c))=
        (W.field G).decode ((tables G P).edge j b c) := by
  cases b <;> cases c <;>
    simp [tables,QuaternaryOrdinaryCompanion.tables,binary,wire,
      GlobalCloseCompletionA0Workfield.z,Fintype.sum_prod_type,Signature.equality]

def subdivide : LengthControlledOracleReduction
    (inputEncoding G P) (W.field G).encoding
    (RawClosedNetwork.validatedEncoding (P.count+1) 1 (extendedArity G P)) (W.field G).encoding
    (value G P) ((extendedTables G P).evaluate (W.field G)) :=
  controlledOneQueryOfEq (EdgeSubdivision.Compiler.computes P.count 1 P.arity)
    (identityComputes (W.field G).encoding) ((extendedTables G P).outputBound (W.field G))
    (value G P) (fun r => (EdgeSubdivision.evaluate_subdivision
      (W.field G) (tables G P) (binary G) (wire G) (fuse G P) r).symm)

def source : LengthControlledOracleReduction
    (inputEncoding G P) (W.field G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P) (OriginalForestSource.value G) :=
  Programme.compose (subdivide G P) (extendedSource G P)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0OrdinarySource
end
