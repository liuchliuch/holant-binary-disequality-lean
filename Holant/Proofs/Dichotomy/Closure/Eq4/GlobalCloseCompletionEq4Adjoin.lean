import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Graph
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Hardness.GeneralEOPinnedDescentAccess
import Holant.Proofs.Closure.ProgrammeCompose

/-! Literal normalized Eq4 adjoin over the original current field. The
actual scalar-Eq4 graph is expanded at every source occurrence and the SAME
nonzero scalar is corrected by the occurrence counter. All old labels remain
literal, and the final oracle is original G. No normalized gadget is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Adjoin
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (d : GlobalCloseCompletionEq4Graph.Output G P)

abbrev F := OI.presentation G
abbrev baseTables := OriginalLCodec.tables P.table
abbrev template := d.labels.template
abbrev arity := sourceArity (Adjoin.templates P.count P.arity (template G P d))
abbrev coordinates := ScaledAdjoin.coordinates (F G) (baseTables G P)
  (template G P d) d.labels.wellFormed d.scalar
abbrev tables := sourceTables (Adjoin.templates P.count P.arity (template G P d))
  (baseTables G P) (coordinates G P d)
def signatures (i : Fin (P.count+1)) : Signature (OI.K G) (arity G P d i.val) :=
  fun x => (F G).decode ((tables G P d).vertex i x)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P d)
abbrev value := (tables G P d).evaluate (F G)

theorem base_signatures : (fun i x => (F G).decode ((baseTables G P).vertex i x))=P.table := by
  funext i x
  simp [baseTables,OriginalLCodec.tables,
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction.targetTables,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]

theorem base_edges : (fun j x y => (F G).decode ((baseTables G P).edge j x y))=
    (fun _ : Fin 1 => Signature.disequality) := by
  funext j x y
  simp [baseTables,OriginalLCodec.tables,
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction.targetTables,
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables]

theorem macro_exact : ((template G P d).network d.labels.wellFormed
    (fun i x => (F G).decode ((baseTables G P).vertex i x))
    (fun j x y => (F G).decode ((baseTables G P).edge j x y))).denote=
      d.scalar • Holant.EightVertex.ProductAnchor.equalityFour := by
  rw [base_signatures,base_edges]
  exact (GeneralEOPinnedDescentAccess.template_denote P.table d.network d.labels d.exact d.native).trans d.denote

private def decodeAny (f : AnySignature (Fin (Module.finrank ℚ (OI.K G)) → ℚ)) :
    AnySignature (OI.K G) := ⟨f.1,fun x => (F G).decode (f.2 x)⟩

def oldLabel (i : Fin P.count) : Fin (P.count+1) := ⟨i.val,by omega⟩
def eq4Label : Fin (P.count+1) := ⟨P.count,Nat.lt_succ_self _⟩

theorem old_signature (i : Fin P.count) :
    (⟨arity G P d (oldLabel G P i).val,signatures G P d (oldLabel G P i)⟩ : AnySignature (OI.K G))=
      ⟨P.arity i.val,P.table i⟩ := by
  have h : (⟨arity G P d (oldLabel G P i).val,coordinates G P d (oldLabel G P i)⟩ :
      AnySignature (Fin (Module.finrank ℚ (OI.K G)) → ℚ))=⟨P.arity i.val,(baseTables G P).vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (template G P d) i)
      (ScaledAdjoin.old_coordinates (F G) (baseTables G P) (template G P d) d.labels.wellFormed d.scalar i)
  have result := congrArg (decodeAny G) h
  exact result.trans (congrArg (fun f => (⟨P.arity i.val,f⟩ : AnySignature (OI.K G)))
    (congrFun (base_signatures G P) i))

theorem eq4_signature :
    (⟨arity G P d (eq4Label G P).val,signatures G P d (eq4Label G P)⟩ : AnySignature (OI.K G))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  have h : (⟨arity G P d (eq4Label G P).val,coordinates G P d (eq4Label G P)⟩ :
      AnySignature (Fin (Module.finrank ℚ (OI.K G)) → ℚ))=
      ⟨4,fun x => (F G).decode.symm
        (((template G P d).network d.labels.wellFormed
          (fun i x => (F G).decode ((baseTables G P).vertex i x))
          (fun j x y => (F G).decode ((baseTables G P).edge j x y))).denote x/d.scalar)⟩ :=
    Sigma.ext (Adjoin.new_boundary (template G P d))
      (ScaledAdjoin.new_coordinates (F G) (baseTables G P) (template G P d) d.labels.wellFormed d.scalar)
  refine (congrArg (decodeAny G) h).trans ?_
  unfold decodeAny
  congr 1
  funext x
  change (F G).decode ((F G).decode.symm _)=_
  rw [LinearEquiv.apply_symm_apply,macro_exact]
  exact mul_div_cancel_left₀ _ d.nonzero

theorem native_edges : ∀j x y,(F G).decode ((tables G P d).edge j x y)=Signature.disequality x y :=
  fun j x y => congrFun₂ (congrFun (base_edges G P) j) x y

theorem original_tables : OriginalLCodec.tables (signatures G P d)=tables G P d := by
  unfold OriginalLCodec.tables
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction.targetTables
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
  congr 1
  · funext i x
    exact (F G).decode.symm_apply_apply _

def remove : LengthControlledOracleReduction (inputEncoding G P d) (F G).encoding
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (F G).encoding
    (value G P d) (OriginalLCodec.value P.table) :=
  Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin (F G) (baseTables G P)
    (template G P d) d.labels.wellFormed d.scalar d.nonzero

def toOriginal : LengthControlledOracleReduction (inputEncoding G P d) (F G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (OriginalLCodec.value (signatures G P d)) (OriginalForestSource.value G) := by
  have source := Programme.compose (remove G P d) P.toOriginal.controlled
  simpa only [OriginalLCodec.value,original_tables] using source

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Adjoin
end
