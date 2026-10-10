import Holant.Proofs.Dichotomy.Closure.Mixed.GlobalCloseCompletionMixedEOModel
import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenRowBasis
import Holant.Proofs.Hardness.GeneralEOUniversalSource

/-! One physical mixed-arity source and one selected class for all local EO
models. In particular binary models and sparse q4 models cannot choose their
tractable classes independently. The actual joint macro compiler ends at the
original-G oracle and retains full length control. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMixedEOSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open GlobalCloseCompletionMixedEOModel
namespace M
export GlobalCloseCompletionMacroFamily (mapped family source)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s t : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (row : Fin t → AnySignature AlgebraicComplex)
variable (models : ∀i,Model G P (row i))

def templates (k : ℕ) : Template :=
  if h : k<t then (models ⟨k,h⟩).labels.template else ⟨0,[],[]⟩

theorem templates_at (i : Fin t) : templates G P row models i.val=(models i).labels.template := by
  simp only [templates,dite_eq_left i.isLt]

theorem valid : ∀k<t,(templates G P row models k).WellFormed P.count 1 P.arity := by
  intro k hk
  rw [templates_at G P row models ⟨k,hk⟩]
  exact (models ⟨k,hk⟩).labels.wellFormed

abbrev table := M.family G P (templates G P row models) (valid G P row models)
abbrev family := EONegativePairReduction.family (table G P row models)
def originalFamily : SignatureFamily AlgebraicComplex := Set.range row

private theorem template_any_congr (T U : Template) (h : T=U)
    (ht : T.WellFormed P.count 1 P.arity) (hu : U.WellFormed P.count 1 P.arity) :
    (⟨T.boundary,(T.network ht (M.mapped G P) (fun _ : Fin 1 => Signature.disequality)).denote⟩ :
      AnySignature AlgebraicComplex)=
    ⟨U.boundary,(U.network hu (M.mapped G P) (fun _ : Fin 1 => Signature.disequality)).denote⟩ := by
  cases h
  rfl

theorem signature_exact (i : Fin t) :
    EONegativePairReduction.signature (table G P row models) i=
      ⟨(row i).1,(models i).graph.denote⟩ := by
  have ht := template_any_congr G P (templates G P row models i.val)
    (models i).labels.template (templates_at G P row models i)
    (valid G P row models i.val i.isLt) (models i).labels.wellFormed
  have hg := GeneralEOPinnedDescentAccess.template_denote (M.mapped G P)
    (models i).graph (models i).labels (models i).exact (models i).native
  exact ht.trans (congrArg (fun f => (⟨(row i).1,f⟩ : AnySignature AlgebraicComplex)) hg)

theorem central (i : Fin t) : Signature.CentralSupport (table G P row models i) :=
  (congrArg (fun f : AnySignature AlgebraicComplex => Signature.CentralSupport f.2)
    (signature_exact G P row models i)).mpr (models i).central

theorem preprocessed : Preprocessed (family G P row models) := by
  rintro _ ⟨i,rfl⟩
  exact (congrArg (fun f : AnySignature AlgebraicComplex => 0<f.1 ∧ f.2≠0)
    (signature_exact G P row models i)).mpr ⟨(models i).positive,(models i).nonzero⟩

theorem common_class (tract : EOTract (preprocess (family G P row models))) :
    ∃C : EOClass,∀i,C.Holds (row i).2 := by
  rw [preprocess_eq_self (preprocessed G P row models)] at tract
  obtain ⟨_,_,sign,C,hs,hC⟩ := tract
  refine ⟨C,fun i => ?_⟩
  have mem : EONegativePairReduction.signature (table G P row models) i∈family G P row models := ⟨i,rfl⟩
  have support := hs _ mem
  have pairing := hC _ mem
  rw [signature_exact] at support pairing
  exact (models i).reconstruct sign C support pairing

theorem common_basis (tract : EOTract (preprocess (family G P row models))) :
    IsCommonKBasis affineClass (originalFamily row) InvertibleKernel.identity ∨
    IsCommonKBasis productClass (originalFamily row) InvertibleKernel.identity := by
  obtain ⟨C,hC⟩ := common_class G P row models tract
  cases C with
  | affine =>
      left
      refine ⟨?_,?_⟩
      · change Affine (kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix))
        simpa [InvertibleKernel.identity,Kernel.pullback] using StableCurrentEvenRowBasis.native_edge_affine
      · rintro _ ⟨i,rfl⟩
        change Affine (InvertibleKernel.identity.symm.action (row i).2)
        simpa [EOClass.Holds] using hC i
  | product =>
      right
      refine ⟨?_,?_⟩
      · change Product (kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix))
        simpa [InvertibleKernel.identity,Kernel.pullback] using StableCurrentEvenRowBasis.native_edge_product
      · rintro _ ⟨i,rfl⟩
        change Product (InvertibleKernel.identity.symm.action (row i).2)
        simpa [EOClass.Holds] using hC i

abbrev OriginalHard : Prop := Holant.LocalDrafts.CountingHardness.WitnessCountingHard
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)
variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}
variable (negative : ¬EOTract (preprocess (family G P row models)))
attribute [local irreducible] GeneralEOUniversalSource.source M.source

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction
    ea encodingNatBool (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  Programme.compose (GeneralEOUniversalSource.source (table G P row models)
    (central G P row models) negative w)
    (M.source G P (templates G P row models) (valid G P row models))

include negative in
theorem witnessCountingHard : OriginalHard G := by
  intro α ea f w
  exact ⟨(source G P row models negative w).reduction⟩

include models in
theorem common_basis_or_hard :
    (IsCommonKBasis affineClass (originalFamily row) InvertibleKernel.identity ∨
      IsCommonKBasis productClass (originalFamily row) InvertibleKernel.identity) ∨ OriginalHard G := by
  classical
  by_cases tract : EOTract (preprocess (family G P row models))
  · exact Or.inl (common_basis G P row models tract)
  · exact Or.inr (witnessCountingHard G P row models tract)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMixedEOSource
end
