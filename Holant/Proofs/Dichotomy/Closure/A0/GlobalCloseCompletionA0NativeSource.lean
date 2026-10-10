import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0XSource
import Holant.Complexity.EdgeSubdivision.WireEquivalence
import Holant.Complexity.EdgeSubdivision.WireFamily

/-! Exact native-X access in the original-field Hadamard coordinates. A proved two-stage wire
substitution exchanges the ordinary source's actual literal X vertex and equality
edge. The resulting family contains every original Hadamard-normalized row and a
literal identity vertex. This constructs source access, without declaring the
new family a saturated native palette or assuming its complete group. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0NativeSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionA0Workfield (K field table)
export GlobalCloseCompletionA0OrdinarySource (tables)
end W
namespace O
export GlobalCloseCompletionA0XSource
  (arity table tables source literal_arity oldLabel xLabel old_signature x_signature)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (d : GlobalCloseCompletionA0XSource.Row G P)

abbrev arity := EdgeSubdivision.targetArity P.count P.arity
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P)
abbrev wireTables := EdgeSubdivision.WireEquivalence.tables (W.field G) (W.tables G P).vertex
abbrev tables := wireTables G P false true
abbrev value := (tables G P).evaluate (W.field G)
def table (i : Fin (P.count+1)) : Signature (W.K G) (arity G P i.val) :=
  fun x => (W.field G).decode ((tables G P).vertex i x)

private def retype {b : ℕ → ℕ} (h : O.arity G P d=b) :
    ExactSignatureTables (Module.finrank ℚ (W.K G)) (P.count+1) 1 b := h ▸ O.tables G P d

private theorem retype_vertex {b : ℕ → ℕ} (h : O.arity G P d=b) (i : Fin (P.count+1)) :
    (⟨b i.val,fun x => (W.field G).decode ((retype G P d h).vertex i x)⟩ : AnySignature (W.K G))=
      ⟨O.arity G P d i.val,O.table G P d i⟩ := by
  cases h
  rfl

private theorem retype_edge {b : ℕ → ℕ} (h : O.arity G P d=b) :
    (retype G P d h).edge=(O.tables G P d).edge := by
  cases h
  rfl

private def retypeSource {b : ℕ → ℕ} (h : O.arity G P d=b) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (P.count+1) 1 b) (W.field G).encoding
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
      ((retype G P d h).evaluate (W.field G)) (OriginalForestSource.value G) := by
  cases h
  exact O.source G P d

private theorem tables_ext {n c d : ℕ} {b : ℕ → ℕ}
    {T U : ExactSignatureTables n c d b} (hv : T.vertex=U.vertex) (he : T.edge=U.edge) : T=U := by
  cases T
  cases U
  cases hv
  cases he
  rfl

private theorem base_vertex : (fun i x => (W.field G).decode ((W.tables G P).vertex i x))=W.table G P := by
  funext i x
  exact LinearEquiv.apply_symm_apply _ _

private theorem old_wire (p q : Bool) (i : Fin P.count) :
    (⟨arity G P (Fin.castAdd 1 i).val,
      fun x => (W.field G).decode ((wireTables G P p q).vertex (Fin.castAdd 1 i) x)⟩ :
        AnySignature (W.K G))=⟨P.arity i.val,W.table G P i⟩ := by
  have hd := congrFun (EdgeSubdivision.WireEquivalence.decoded_signatures
    (W.field G) (W.tables G P).vertex p) (Fin.castAdd 1 i)
  rw [base_vertex] at hd
  exact (congrArg (fun f : Signature (W.K G) (arity G P (Fin.castAdd 1 i).val) =>
    (⟨arity G P (Fin.castAdd 1 i).val,f⟩ : AnySignature (W.K G))) hd).trans
      (Sigma.ext (by simp [arity,EdgeSubdivision.targetArity,i.isLt])
        (EdgeSubdivision.extendedSignatures_old_heq (W.table G P)
          (fun _ : Fin 1 => EdgeSubdivision.WirePath.kernel p) i))

private theorem new_wire (p q : Bool) :
    (⟨arity G P (O.xLabel G P).val,
      fun x => (W.field G).decode ((wireTables G P p q).vertex (O.xLabel G P) x)⟩ :
        AnySignature (W.K G))=⟨2,fun x => EdgeSubdivision.WirePath.kernel p (x 0) (x 1)⟩ := by
  have label : O.xLabel G P=Fin.natAdd P.count (0 : Fin 1) := rfl
  rw [label]
  have hd := congrFun (EdgeSubdivision.WireEquivalence.decoded_signatures
    (W.field G) (W.tables G P).vertex p) (Fin.natAdd P.count (0 : Fin 1))
  rw [base_vertex] at hd
  exact (congrArg (fun f : Signature (W.K G) (arity G P P.count) =>
    (⟨arity G P P.count,f⟩ : AnySignature (W.K G))) hd).trans
      (Sigma.ext (by simp [arity,EdgeSubdivision.targetArity])
        (EdgeSubdivision.extendedSignatures_new_heq (W.table G P)
          (fun _ : Fin 1 => EdgeSubdivision.WirePath.kernel p) (0 : Fin 1)))

private theorem ordinary_tables : retype G P d (O.literal_arity G P d)=wireTables G P true false := by
  apply tables_ext
  · funext i x
    apply (W.field G).decode.injective
    have h : (⟨arity G P i.val,
        fun y => (W.field G).decode ((retype G P d (O.literal_arity G P d)).vertex i y)⟩ :
          AnySignature (W.K G))=⟨arity G P i.val,
            fun y => (W.field G).decode ((wireTables G P true false).vertex i y)⟩ := by
      refine (retype_vertex G P d (O.literal_arity G P d) i).trans ?_
      by_cases hi : i.val<P.count
      · have label : i=O.oldLabel G P ⟨i.val,hi⟩ := Fin.ext rfl
        rw [label]
        exact (O.old_signature G P d ⟨i.val,hi⟩).trans (old_wire G P true false ⟨i.val,hi⟩).symm
      · have label : i=O.xLabel G P := Fin.ext (by change i.val=P.count; have := i.isLt; omega)
        rw [label]
        exact (O.x_signature G P d).trans (by simpa only [EdgeSubdivision.kernel_true] using
          (new_wire G P true false).symm)
    exact congrFun (eq_of_heq (Sigma.mk.inj_iff.mp h).2) x
  · rw [retype_edge]
    funext i b c
    change (W.field G).decode.symm (Signature.equality b c)=
      (W.field G).decode.symm (EdgeSubdivision.WirePath.kernel false b c)
    rw [EdgeSubdivision.kernel_false]

def ordinarySource : LengthControlledOracleReduction
    (inputEncoding G P) (W.field G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((wireTables G P true false).evaluate (W.field G)) (OriginalForestSource.value G) := by
  have r := retypeSource G P d (O.literal_arity G P d)
  rw [ordinary_tables] at r
  exact r

def swap : LengthControlledOracleReduction
    (inputEncoding G P) (W.field G).encoding
    (inputEncoding G P) (W.field G).encoding
    (value G P) ((wireTables G P true false).evaluate (W.field G)) :=
  controlledOneQueryOfEq (EdgeSubdivision.WireEquivalence.computes P.count P.arity)
    (identityComputes (W.field G).encoding) ((wireTables G P true false).outputBound (W.field G))
    (value G P) (fun r => by
      rw [value,EdgeSubdivision.WireEquivalence.evaluate_eq,EdgeSubdivision.WireEquivalence.evaluate_eq,base_vertex]
      exact (EdgeSubdivision.WireEquivalence.query_value (W.table G P) false true r).symm)

def source : LengthControlledOracleReduction
    (inputEncoding G P) (W.field G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P) (OriginalForestSource.value G) := Programme.compose (swap G P) (ordinarySource G P d)

theorem old_signature (i : Fin P.count) :
    (⟨arity G P (O.oldLabel G P i).val,table G P (O.oldLabel G P i)⟩ : AnySignature (W.K G))=
      ⟨P.arity i.val,W.table G P i⟩ := old_wire G P false true i

theorem identity_signature :
    (⟨arity G P (O.xLabel G P).val,table G P (O.xLabel G P)⟩ : AnySignature (W.K G))=
      ⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := by
  exact (new_wire G P false true).trans
    (congrArg (fun B : Kernel (W.K G) =>
      (⟨2,fun x => B (x 0) (x 1)⟩ : AnySignature (W.K G))) EdgeSubdivision.kernel_false)

theorem native_edges (i : Fin 1) (b c : Bool) :
    (W.field G).decode ((tables G P).edge i b c)=Signature.disequality b c := by
  change (W.field G).decode ((W.field G).decode.symm (EdgeSubdivision.WirePath.kernel true b c))=_
  rw [LinearEquiv.apply_symm_apply,EdgeSubdivision.kernel_true]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0NativeSource
end
