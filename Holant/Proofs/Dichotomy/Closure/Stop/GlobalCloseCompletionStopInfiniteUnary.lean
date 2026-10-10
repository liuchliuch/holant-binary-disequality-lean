import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopInfiniteSource
import Holant.Proofs.Hardness.EONegativeSubfamily

/-! Public infinite-stop supply with exactly the old current rows and the two
produced nonzero unaries. The auxiliary spectral H label is omitted by an
actual finite literal-label query and its coefficient-field retraction. All
stages remain length-controlled through the unchanged original-G oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteUnary
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure hiding binarySignature
open Holant.LocalDrafts.BinaryInterpolation Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionStopInfiniteSource (count arity table left right old_literal left_literal right_literal
  left_nonzero right_nonzero toOriginal)
end S
namespace L
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativeSubfamily
  (label selected selectedArity controlled)
end L
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue target_exact)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B)
variable (infinite : ¬ProjectivelyFinite (transfer B))

abbrev count := P.count+2
def select (k : ℕ) : ℕ := if k<P.count then k else k+1

theorem select_bound (i : Fin (count G P)) : select G P i.val<S.count G P := by
  unfold select S.count count
  split_ifs <;> have := i.isLt <;> omega

abbrev label := L.label (select G P) (select_bound G P)
abbrev arity := L.selectedArity (a:=S.arity G P) (select G P)
abbrev table := L.selected (S.table G P B actual infinite) (select G P) (select_bound G P)
abbrev field := O.originalField (table G P B actual infinite)
abbrev presentation := O.originalPresentation (table G P B actual infinite)
abbrev value := O.originalValue (table G P B actual infinite)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P)

theorem old_label (i : Fin P.count) : label G P ⟨i.val,by dsimp only [count,S.count] at *; omega⟩=⟨i.val,by dsimp only [count,S.count] at *; omega⟩ := by
  apply Fin.ext
  simp [label,L.label,select,i.isLt]

theorem left_label : label G P ⟨P.count,by dsimp only [count,S.count] at *; omega⟩=⟨P.count+1,by dsimp only [count,S.count] at *; omega⟩ := by
  apply Fin.ext
  simp [label,L.label,select]

theorem right_label : label G P ⟨P.count+1,by dsimp only [count,S.count] at *; omega⟩=⟨(P.count+1)+1,by dsimp only [count,S.count] at *; omega⟩ := by
  apply Fin.ext
  simp [label,L.label,select]

theorem selected_literal (i : Fin (count G P)) :
    (⟨arity G P i.val,table G P B actual infinite i⟩ : AnySignature AlgebraicComplex)=
      ⟨S.arity G P (label G P i).val,S.table G P B actual infinite (label G P i)⟩ := rfl

theorem old_literal (i : Fin P.count) :
    (⟨arity G P i.val,table G P B actual infinite ⟨i.val,by dsimp only [count,S.count] at *; omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨P.arity i.val,GlobalCloseCompletionStopInfiniteSpectral.mapped G P i⟩ := by
  refine (selected_literal G P B actual infinite ⟨i.val,by dsimp only [count]; omega⟩).trans ?_
  exact (congrArg (fun j : Fin (S.count G P)=>
    (⟨S.arity G P j.val,S.table G P B actual infinite j⟩ : AnySignature AlgebraicComplex))
    (old_label G P i)).trans (S.old_literal G P B actual infinite i)

theorem left_literal :
    (⟨arity G P P.count,table G P B actual infinite ⟨P.count,by dsimp only [count,S.count] at *; omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨1,fun z=>S.left G P B actual infinite (z 0)⟩ := by
  refine (selected_literal G P B actual infinite ⟨P.count,by dsimp only [count]; omega⟩).trans ?_
  exact (congrArg (fun j : Fin (S.count G P)=>
    (⟨S.arity G P j.val,S.table G P B actual infinite j⟩ : AnySignature AlgebraicComplex))
    (left_label G P)).trans (S.left_literal G P B actual infinite)

theorem right_literal :
    (⟨arity G P (P.count+1),table G P B actual infinite ⟨P.count+1,by dsimp only [count,S.count] at *; omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨1,fun z=>S.right G P B actual infinite (z 0)⟩ := by
  refine (selected_literal G P B actual infinite ⟨P.count+1,by dsimp only [count]; omega⟩).trans ?_
  exact (congrArg (fun j : Fin (S.count G P)=>
    (⟨S.arity G P j.val,S.table G P B actual infinite j⟩ : AnySignature AlgebraicComplex))
    (right_label G P)).trans (S.right_literal G P B actual infinite)

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin (count G P)=>
  (⟨arity G P i.val,table G P B actual infinite i⟩ : AnySignature AlgebraicComplex)

theorem family_exact : family G P B actual infinite=
    UnifiedSource.gamma (GlobalCloseCompletionStopInfiniteSpectral.mapped G P) ∪
      {⟨1,fun z=>S.left G P B actual infinite (z 0)⟩,⟨1,fun z=>S.right G P B actual infinite (z 0)⟩} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<P.count
    · exact Or.inl ⟨⟨i.val,hi⟩,(old_literal G P B actual infinite ⟨i.val,hi⟩).symm⟩
    · by_cases he : i.val=P.count
      · have eq : i=⟨P.count,by dsimp only [count,S.count] at *; omega⟩ := Fin.ext he
        rw [eq]
        exact Or.inr (Or.inl (left_literal G P B actual infinite))
      · have eq : i=⟨P.count+1,by dsimp only [count,S.count] at *; omega⟩ := Fin.ext (by change i.val=P.count+1; have := i.isLt; dsimp only [count,S.count] at *; omega)
        rw [eq]
        exact Or.inr (Or.inr (right_literal G P B actual infinite))
  · rintro (⟨i,rfl⟩|hf)
    · exact ⟨⟨i.val,by dsimp only [count,S.count] at *; omega⟩,old_literal G P B actual infinite i⟩
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
      rcases hf with rfl|rfl
      · exact ⟨⟨P.count,by dsimp only [count,S.count] at *; omega⟩,left_literal G P B actual infinite⟩
      · exact ⟨⟨P.count+1,by dsimp only [count,S.count] at *; omega⟩,right_literal G P B actual infinite⟩

abbrev left := S.left G P B actual infinite
abbrev right := S.right G P B actual infinite

theorem left_nonzero : (fun z : Fin 1→Bool=>left G P B actual infinite (z 0))≠0 :=
  S.left_nonzero G P B actual infinite

theorem right_nonzero : (fun z : Fin 1→Bool=>right G P B actual infinite (z 0))≠0 :=
  S.right_nonzero G P B actual infinite

theorem left_actual : Gadget.Realizes (family G P B actual infinite) .disequality
    (fun z : Fin 1→Bool=>left G P B actual infinite (z 0)) :=
  Gadget.realizes_of_mem _ _ _ ⟨⟨P.count,by dsimp only [count]; omega⟩,
    left_literal G P B actual infinite⟩

theorem right_actual : Gadget.Realizes (family G P B actual infinite) .disequality
    (fun z : Fin 1→Bool=>right G P B actual infinite (z 0)) :=
  Gadget.realizes_of_mem _ _ _ ⟨⟨P.count+1,by dsimp only [count]; omega⟩,
    right_literal G P B actual infinite⟩

/-- The source coefficient field is now generated by Γ,u,v alone. No separate H label
or macro-scale generators are added. -/
def toOriginal : LengthControlledOracleReduction
    (inputEncoding G P) (presentation G P B actual infinite).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P B actual infinite) (OriginalForestSource.value G) :=
  Programme.compose (L.controlled (S.table G P B actual infinite) (select G P) (select_bound G P))
    (S.toOriginal G P B actual infinite)

def physical := PhysicalProgramme.ofControlled (toOriginal G P B actual infinite)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteUnary
end
