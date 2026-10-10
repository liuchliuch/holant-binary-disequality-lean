import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBWorkfield
import Holant.Proofs.Closure.ClosureBStableMatrix

/-! The actual B-normalized whole-current ordinary source has a literal X
vertex. Its scalar is removed by an occurrence-counted adjoin of the current
identity label; no analytic normalized binary becomes an assumed resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBOrdinarySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionBWorkfield (K field mapped imaginary imaginary_value table table_value tables value source)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
local instance : Algebra ℚ (W.K G P) := (W.K G P).algebra'

def scalar : W.K G P := W.imaginary G P/2
theorem scalar_value : (W.K G P).val (scalar G P)=imaginaryUnit/2 := by
  simp [scalar,W.imaginary_value,map_ofNat]
theorem scalar_nonzero : scalar G P≠0 := by
  intro h
  have hn : (imaginaryUnit/2 : AlgebraicComplex)≠0 := div_ne_zero Holant.Marked.imaginaryUnit_ne_zero (by norm_num)
  exact hn ((scalar_value G P).symm.trans (by rw [h,map_zero]))

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
    (⟨P.arity (label G P).val,W.table G P (label G P)⟩ : AnySignature (W.K G P))=
      ⟨2,fun x => scalar G P*Signature.disequality (x 0) (x 1)⟩ := by
  apply mapAny_injective (W.K G P).val.toRingHom
  have ht : RingHomRealization.mapAny (W.K G P).val.toRingHom
      ⟨P.arity (label G P).val,W.table G P (label G P)⟩=
        (⟨P.arity (label G P).val,Holant.Marked.basisB.symm.action (W.mapped G P (label G P))⟩ :
          AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex (P.arity (label G P).val) =>
      (⟨P.arity (label G P).val,f⟩ : AnySignature AlgebraicComplex))
    exact funext (W.table_value G P (label G P))
  refine ht.trans ?_
  have hm := congrArg (fun f : AnySignature AlgebraicComplex =>
    (⟨f.1,Holant.Marked.basisB.symm.action f.2⟩ : AnySignature AlgebraicComplex)) (mapped_identity G P)
  refine hm.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  rw [ClosureBStable.inverse_equality_signature]
  funext x
  change (imaginaryUnit/2)*Signature.disequality (x 0) (x 1)=
    (W.K G P).val (scalar G P*Signature.disequality (x 0) (x 1))
  rw [map_mul,scalar_value]
  cases x 0 <;> cases x 1 <;> simp [Signature.disequality]

def graph : Network (W.K G P) 2 :=
  Network.corolla (fun x => scalar G P*Signature.disequality (x 0) (x 1))
def labels : Labelling (graph G P).shape P.count 1 P.arity where
  vertex _ := label G P
  vertex_arity _ := congrArg Sigma.fst (identity_row G P)
  edge := Fin.elim0
abbrev template := (labels G P).template
abbrev arity := sourceArity (Adjoin.templates P.count P.arity (template G P))
abbrev coordinates := ScaledAdjoin.coordinates (W.field G P) (W.tables G P)
  (template G P) (labels G P).wellFormed (scalar G P)
abbrev tables := sourceTables (Adjoin.templates P.count P.arity (template G P))
  (W.tables G P) (coordinates G P)
def table (i : Fin (P.count+1)) : Signature (W.K G P) (arity G P i.val) :=
  fun x => (W.field G P).decode ((tables G P).vertex i x)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P)
abbrev value := (tables G P).evaluate (W.field G P)

theorem macro_denote : ((template G P).network (labels G P).wellFormed
    (W.table G P) (fun _ : Fin 1 => Signature.equality)).denote=
      fun x : Fin 2 → Bool => scalar G P*Signature.disequality (x 0) (x 1) := by
  rw [Labelling.denote_template]
  trans (graph G P).denote
  · apply Network.denote_congr
    · intro v x
      exact BinaryInterpolation.Chains.signature_cast_apply _ _ (identity_row G P)
        (congrArg Sigma.fst (identity_row G P)) x
    · intro e b c
      exact Fin.elim0 e
  · exact Network.denote_corolla _

private def decodeAny (f : AnySignature (Fin (Module.finrank ℚ (W.K G P)) → ℚ)) :
    AnySignature (W.K G P) := ⟨f.1,fun x => (W.field G P).decode (f.2 x)⟩

def oldLabel (i : Fin P.count) : Fin (P.count+1) := Fin.castAdd 1 i
def xLabel : Fin (P.count+1) := ⟨P.count,Nat.lt_succ_self _⟩

theorem old_signature (i : Fin P.count) :
    (⟨arity G P (oldLabel G P i).val,table G P (oldLabel G P i)⟩ : AnySignature (W.K G P))=
      ⟨P.arity i.val,W.table G P i⟩ := by
  have h : (⟨arity G P (oldLabel G P i).val,coordinates G P (oldLabel G P i)⟩ :
      AnySignature (Fin (Module.finrank ℚ (W.K G P)) → ℚ))=
      ⟨P.arity i.val,(W.tables G P).vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (template G P) i)
      (ScaledAdjoin.old_coordinates (W.field G P) (W.tables G P) (template G P)
        (labels G P).wellFormed (scalar G P) i)
  exact congrArg (decodeAny G P) h

theorem x_signature :
    (⟨arity G P (xLabel G P).val,table G P (xLabel G P)⟩ : AnySignature (W.K G P))=
      ⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ := by
  have h : (⟨arity G P (xLabel G P).val,coordinates G P (xLabel G P)⟩ :
      AnySignature (Fin (Module.finrank ℚ (W.K G P)) → ℚ))=
      ⟨2,fun x => (W.field G P).decode.symm
        (((template G P).network (labels G P).wellFormed
          (fun i x => (W.field G P).decode ((W.tables G P).vertex i x))
          (fun j b c => (W.field G P).decode ((W.tables G P).edge j b c))).denote x/scalar G P)⟩ :=
    Sigma.ext (Adjoin.new_boundary (template G P))
      (ScaledAdjoin.new_coordinates (W.field G P) (W.tables G P) (template G P)
        (labels G P).wellFormed (scalar G P))
  refine (congrArg (decodeAny G P) h).trans ?_
  apply congrArg (fun f : Signature (W.K G P) 2 => (⟨2,f⟩ : AnySignature (W.K G P)))
  funext x
  change (W.field G P).decode ((W.field G P).decode.symm _)=_
  rw [LinearEquiv.apply_symm_apply]
  have edge : (fun j b c => (W.field G P).decode ((W.tables G P).edge j b c))=
      (fun _ : Fin 1 => Signature.equality) := by
    funext j b c
    exact LinearEquiv.apply_symm_apply _ _
  rw [edge]
  exact (congrArg (fun z : W.K G P => z/scalar G P)
    (congrFun (macro_denote G P) x)).trans
      (mul_div_cancel_left₀ _ (scalar_nonzero G P))

theorem literal_arity : arity G P=EdgeSubdivision.targetArity P.count P.arity := by
  funext i
  by_cases hi : i<P.count <;>
    simp [arity,sourceArity,Adjoin.templates,EdgeSubdivision.targetArity,identityTemplate,hi]

def source : LengthControlledOracleReduction
    (inputEncoding G P) (W.field G P).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P) (OriginalForestSource.value G) :=
  Programme.compose
    (Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin (W.field G P) (W.tables G P)
      (template G P) (labels G P).wellFormed (scalar G P) (scalar_nonzero G P)) (W.source G P)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBOrdinarySource
end
