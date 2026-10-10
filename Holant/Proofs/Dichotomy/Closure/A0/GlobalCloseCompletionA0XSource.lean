import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0OrdinarySource
import Holant.Marked.Fusion

/-! Actual literal X adjoin to the whole ordinary Hadamard source. The row
receipt identifies an existing normalized current label and its original-field
nonzero multiplier; every X occurrence uses the charged substitution. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0XSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionA0Workfield (K field table)
export GlobalCloseCompletionA0OrdinarySource (tables value source)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

structure Row where
  label : Fin P.count
  scalar : W.K G
  nonzero : scalar≠0
  literal : (⟨P.arity label.val,W.table G P label⟩ : AnySignature (W.K G))=
    ⟨2,fun x => scalar*Signature.disequality (x 0) (x 1)⟩

variable (d : Row G P)

def graph : Network (W.K G) 2 :=
  Network.corolla (fun x => d.scalar*Signature.disequality (x 0) (x 1))
def labels : Labelling (graph G P d).shape P.count 1 P.arity where
  vertex _ := d.label
  vertex_arity _ := congrArg Sigma.fst (d.literal)
  edge := Fin.elim0
abbrev template := (labels G P d).template
abbrev arity := sourceArity (Adjoin.templates P.count P.arity (template G P d))
abbrev coordinates := ScaledAdjoin.coordinates (W.field G) (W.tables G P)
  (template G P d) (labels G P d).wellFormed (d.scalar)
abbrev tables := sourceTables (Adjoin.templates P.count P.arity (template G P d))
  (W.tables G P) (coordinates G P d)
def table (i : Fin (P.count+1)) : Signature (W.K G) (arity G P d i.val) :=
  fun x => (W.field G).decode ((tables G P d).vertex i x)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P d)
abbrev value := (tables G P d).evaluate (W.field G)

theorem macro_denote : ((template G P d).network (labels G P d).wellFormed
    (W.table G P) (fun _ : Fin 1 => Signature.equality)).denote=
      fun x : Fin 2 → Bool => d.scalar*Signature.disequality (x 0) (x 1) := by
  rw [Labelling.denote_template]
  trans (graph G P d).denote
  · apply Network.denote_congr
    · intro v x
      exact BinaryInterpolation.Chains.signature_cast_apply _ _ (d.literal)
        (congrArg Sigma.fst (d.literal)) x
    · intro e b c
      exact Fin.elim0 e
  · exact Network.denote_corolla _

private def decodeAny (f : AnySignature (Fin (Module.finrank ℚ (W.K G)) → ℚ)) :
    AnySignature (W.K G) := ⟨f.1,fun x => (W.field G).decode (f.2 x)⟩

def oldLabel (i : Fin P.count) : Fin (P.count+1) := Fin.castAdd 1 i
def xLabel : Fin (P.count+1) := ⟨P.count,Nat.lt_succ_self _⟩

theorem old_signature (i : Fin P.count) :
    (⟨arity G P d (oldLabel G P i).val,table G P d (oldLabel G P i)⟩ : AnySignature (W.K G))=
      ⟨P.arity i.val,W.table G P i⟩ := by
  have h : (⟨arity G P d (oldLabel G P i).val,coordinates G P d (oldLabel G P i)⟩ :
      AnySignature (Fin (Module.finrank ℚ (W.K G)) → ℚ))=
      ⟨P.arity i.val,(W.tables G P).vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (template G P d) i)
      (ScaledAdjoin.old_coordinates (W.field G) (W.tables G P) (template G P d)
        (labels G P d).wellFormed (d.scalar) i)
  refine (congrArg (decodeAny G) h).trans ?_
  apply congrArg (fun f : Signature (W.K G) (P.arity i.val) => (⟨P.arity i.val,f⟩ : AnySignature (W.K G)))
  funext x
  exact LinearEquiv.apply_symm_apply _ _

theorem x_signature :
    (⟨arity G P d (xLabel G P).val,table G P d (xLabel G P)⟩ : AnySignature (W.K G))=
      ⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ := by
  have h : (⟨arity G P d (xLabel G P).val,coordinates G P d (xLabel G P)⟩ :
      AnySignature (Fin (Module.finrank ℚ (W.K G)) → ℚ))=
      ⟨2,fun x => (W.field G).decode.symm
        (((template G P d).network (labels G P d).wellFormed
          (fun i x => (W.field G).decode ((W.tables G P).vertex i x))
          (fun j b c => (W.field G).decode ((W.tables G P).edge j b c))).denote x/d.scalar)⟩ :=
    Sigma.ext (Adjoin.new_boundary (template G P d))
      (ScaledAdjoin.new_coordinates (W.field G) (W.tables G P) (template G P d)
        (labels G P d).wellFormed (d.scalar))
  refine (congrArg (decodeAny G) h).trans ?_
  apply congrArg (fun f : Signature (W.K G) 2 => (⟨2,f⟩ : AnySignature (W.K G)))
  funext x
  change (W.field G).decode ((W.field G).decode.symm _)=_
  rw [LinearEquiv.apply_symm_apply]
  have edge : (fun j b c => (W.field G).decode ((W.tables G P).edge j b c))=
      (fun _ : Fin 1 => Signature.equality) := by
    funext j b c
    exact LinearEquiv.apply_symm_apply _ _
  have vertex : (fun i x => (W.field G).decode ((W.tables G P).vertex i x))=W.table G P := by
    funext i x
    exact LinearEquiv.apply_symm_apply _ _
  rw [edge,vertex]
  exact (congrArg (fun z : W.K G => z/d.scalar)
    (congrFun (macro_denote G P d) x)).trans
      (mul_div_cancel_left₀ _ (d.nonzero))

theorem literal_arity : arity G P d=EdgeSubdivision.targetArity P.count P.arity := by
  funext i
  by_cases hi : i<P.count <;>
    simp [arity,sourceArity,Adjoin.templates,EdgeSubdivision.targetArity,identityTemplate,hi]

def source : LengthControlledOracleReduction
    (inputEncoding G P d) (W.field G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P d) (OriginalForestSource.value G) :=
  Programme.compose
    (Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin (W.field G) (W.tables G P)
      (template G P d) (labels G P d).wellFormed (d.scalar) (d.nonzero)) (W.source G P)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0XSource
end
