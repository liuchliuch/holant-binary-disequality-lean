import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Workfield
import Holant.Marked.Fusion

/-! Literal identity is obtained from the actual retained Hadamard row I/2,
with its nonzero factor removed by the occurrence-counted adjoin programme.
The edge remains the same signed diagonal Z throughout this module. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0IdentityAdjoin
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionA0Workfield (K field mapped basis z table table_value tables value source)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def scalar : W.K G := 1/2
 theorem scalar_nonzero : scalar G≠0 := by norm_num [scalar]

 theorem inverse_equality : W.basis.symm.action (kernelSignature Signature.equality)=
    (1/2 : AlgebraicComplex) • kernelSignature Signature.equality := by
  rw [Holant.Marked.transport_signature]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [Holant.Marked.transport,W.basis,GlobalCloseCompletionA0Workfield.basis,
      ClosureMarkedDihedralA0.basis,ClosureMarkedCyclic.basis,
      Holant.Marked.basisA,Holant.Marked.UAInv,Kernel.mul_apply,Kernel.transpose,
      Signature.equality,Holant.Marked.scale,kernelSignature,Pi.smul_apply,smul_eq_mul,h0,h1]

def label : Fin P.count := P.equality.choose

theorem mapped_identity :
    (⟨P.arity (label G P).val,W.mapped G P (label G P)⟩ : AnySignature AlgebraicComplex)=
      ⟨2,kernelSignature Signature.equality⟩ := by
  have hi : (⟨P.arity (label G P).val,P.table (label G P)⟩ : AnySignature (OI.K G))=
    ⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := P.equality.choose_spec
  have h := congrArg (RingHomRealization.mapAny (StableHigherCurrentPurePinsCore.embedding G).toRingHom) hi
  refine h.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.equality]

private theorem mapAny_injective {L : Type} [Field L] (φ : L →+* AlgebraicComplex) :
    Function.Injective (RingHomRealization.mapAny φ) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (fun f : Signature L n => (⟨n,f⟩ : AnySignature L))
  funext x
  exact φ.injective (congrFun hf x)

theorem identity_row :
    (⟨P.arity (label G P).val,W.table G P (label G P)⟩ : AnySignature (W.K G))=
      ⟨2,fun x => scalar G*Signature.equality (x 0) (x 1)⟩ := by
  apply mapAny_injective (StableHigherCurrentPurePinsCore.embedding G).toRingHom
  have ht : RingHomRealization.mapAny (StableHigherCurrentPurePinsCore.embedding G).toRingHom
      ⟨P.arity (label G P).val,W.table G P (label G P)⟩=
        (⟨P.arity (label G P).val,W.basis.symm.action (W.mapped G P (label G P))⟩ :
          AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex (P.arity (label G P).val) =>
      (⟨P.arity (label G P).val,f⟩ : AnySignature AlgebraicComplex))
    exact funext (W.table_value G P (label G P))
  refine ht.trans ?_
  have hm := congrArg (fun f : AnySignature AlgebraicComplex =>
    (⟨f.1,W.basis.symm.action f.2⟩ : AnySignature AlgebraicComplex)) (mapped_identity G P)
  refine hm.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  rw [inverse_equality]
  funext x
  change (1/2 : AlgebraicComplex)*Signature.equality (x 0) (x 1)=
    StableHigherCurrentPurePinsCore.embedding G (scalar G*Signature.equality (x 0) (x 1))
  have hs : StableHigherCurrentPurePinsCore.embedding G (scalar G)=(1/2 : AlgebraicComplex) := by
    rw [scalar,map_div₀,map_one,map_ofNat]
  rw [map_mul,hs]
  cases x 0 <;> cases x 1 <;> simp [Signature.equality]

def graph : Network (W.K G) 2 :=
  Network.corolla (fun x => scalar G*Signature.equality (x 0) (x 1))
def labels : Labelling (graph G).shape P.count 1 P.arity where
  vertex _ := label G P
  vertex_arity _ := congrArg Sigma.fst (identity_row G P)
  edge := Fin.elim0
abbrev template := (labels G P).template
abbrev arity := sourceArity (Adjoin.templates P.count P.arity (template G P))
abbrev coordinates := ScaledAdjoin.coordinates (W.field G) (W.tables G P)
  (template G P) (labels G P).wellFormed (scalar G)
abbrev tables := sourceTables (Adjoin.templates P.count P.arity (template G P))
  (W.tables G P) (coordinates G P)
def table (i : Fin (P.count+1)) : Signature (W.K G) (arity G P i.val) :=
  fun x => (W.field G).decode ((tables G P).vertex i x)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P)
abbrev value := (tables G P).evaluate (W.field G)

theorem macro_denote : ((template G P).network (labels G P).wellFormed
    (W.table G P) (fun _ : Fin 1 => W.z G)).denote=
      fun x : Fin 2 → Bool => scalar G*Signature.equality (x 0) (x 1) := by
  rw [Labelling.denote_template]
  trans (graph G).denote
  · apply Network.denote_congr
    · intro v x
      exact BinaryInterpolation.Chains.signature_cast_apply _ _ (identity_row G P)
        (congrArg Sigma.fst (identity_row G P)) x
    · intro e b c
      exact Fin.elim0 e
  · exact Network.denote_corolla _

private def decodeAny (f : AnySignature (Fin (Module.finrank ℚ (W.K G)) → ℚ)) :
    AnySignature (W.K G) := ⟨f.1,fun x => (W.field G).decode (f.2 x)⟩

def oldLabel (i : Fin P.count) : Fin (P.count+1) := Fin.castAdd 1 i
def identityLabel : Fin (P.count+1) := ⟨P.count,Nat.lt_succ_self _⟩

theorem old_signature (i : Fin P.count) :
    (⟨arity G P (oldLabel G P i).val,table G P (oldLabel G P i)⟩ : AnySignature (W.K G))=
      ⟨P.arity i.val,W.table G P i⟩ := by
  have h : (⟨arity G P (oldLabel G P i).val,coordinates G P (oldLabel G P i)⟩ :
      AnySignature (Fin (Module.finrank ℚ (W.K G)) → ℚ))=
      ⟨P.arity i.val,(W.tables G P).vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (template G P) i)
      (ScaledAdjoin.old_coordinates (W.field G) (W.tables G P) (template G P)
        (labels G P).wellFormed (scalar G) i)
  exact congrArg (decodeAny G) h

theorem identity_signature :
    (⟨arity G P (identityLabel G P).val,table G P (identityLabel G P)⟩ : AnySignature (W.K G))=
      ⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := by
  have h : (⟨arity G P (identityLabel G P).val,coordinates G P (identityLabel G P)⟩ :
      AnySignature (Fin (Module.finrank ℚ (W.K G)) → ℚ))=
      ⟨2,fun x => (W.field G).decode.symm
        (((template G P).network (labels G P).wellFormed
          (fun i x => (W.field G).decode ((W.tables G P).vertex i x))
          (fun j b c => (W.field G).decode ((W.tables G P).edge j b c))).denote x/scalar G)⟩ :=
    Sigma.ext (Adjoin.new_boundary (template G P))
      (ScaledAdjoin.new_coordinates (W.field G) (W.tables G P) (template G P)
        (labels G P).wellFormed (scalar G))
  refine (congrArg (decodeAny G) h).trans ?_
  apply congrArg (fun f : Signature (W.K G) 2 => (⟨2,f⟩ : AnySignature (W.K G)))
  funext x
  change (W.field G).decode ((W.field G).decode.symm _)=_
  rw [LinearEquiv.apply_symm_apply]
  have edge : (fun j b c => (W.field G).decode ((W.tables G P).edge j b c))=
      (fun _ : Fin 1 => W.z G) := by
    funext j b c
    exact LinearEquiv.apply_symm_apply _ _
  rw [edge]
  exact (congrArg (fun z : W.K G => z/scalar G)
    (congrFun (macro_denote G P) x)).trans
      (mul_div_cancel_left₀ _ (scalar_nonzero G))

theorem literal_arity : arity G P=EdgeSubdivision.targetArity P.count P.arity := by
  funext i
  by_cases hi : i<P.count <;>
    simp [arity,sourceArity,Adjoin.templates,EdgeSubdivision.targetArity,identityTemplate,hi]

def source : LengthControlledOracleReduction
    (inputEncoding G P) (W.field G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P) (OriginalForestSource.value G) :=
  Programme.compose
    (Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin (W.field G) (W.tables G P)
      (template G P) (labels G P).wellFormed (scalar G) (scalar_nonzero G)) (W.source G P)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0IdentityAdjoin
end
