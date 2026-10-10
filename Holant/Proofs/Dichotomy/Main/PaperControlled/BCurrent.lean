import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityOriginal
import Holant.Proofs.Dichotomy.Main.PaperControlled.BSparseEq4
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDescent
import Holant.Proofs.Dichotomy.Retained.StableCurrentBinaryClosure

/-! Actual exhausted B-marking continuation. A sparse prepared q4 is consumed
through its real Eq4 graph and whole-current ordinary CSP source; all higher
occurrences descend to actual q4. Binary-only current families are reconstructed
in Product at the same B basis. Only a dense normalized q4, the genuine ordinary
negative obstruction, whole-family tractability or original-G hardness remains. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.BCurrent
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
namespace BQ
export GlobalCloseCompletionBQuaternary (normalized FullParity SparseOutput sparse_or_full)
end BQ
namespace C
export GlobalCloseCompletionBNativeCodec (mapped)
end C
namespace E
export GlobalCloseCompletionBEqualityOriginal (CurrentTract family classified ordinarySource squareCSPSource)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
abbrev palette := R.final.source.palette
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion))

def Sparse : Prop := ∃o : CurrentOccurrences.Id G (palette G base R),
  ∃four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4,
    ¬∃p : Bool,BQ.FullParity G (Q.table G base four) p

def Dense : Prop := ∃o : CurrentOccurrences.Id G (palette G base R),
  ∃four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4,
    ∃p : Bool,BQ.FullParity G (Q.table G base four) p

include noPrior N in
theorem sparse_eq4_or_hard (sparse : Sparse G base R) :
    Nonempty (GlobalCloseCompletionBPrimeEq4.Output (C.mapped G (palette G base R))) ∨
      PaperControlledHardness.Original G := by
  obtain ⟨o,four,noFull⟩ := sparse
  let q := Q.table G base four
  let core := Q.minimum G base four
  have literal : core.signature=⟨4,q⟩ := Q.minimum_literal G base four
  have stable := Q.matching G base (R.preparationReceipt G base noPrior o) four
  obtain ⟨d⟩ := (BQ.sparse_or_full G (palette G base R) R.final.ready.torsion N
    q core literal stable).resolve_left noFull
  exact PaperControlled.BSparseEq4.eq4_or_hard G (palette G base R) R.final.ready.torsion N
    (fun _ : Fin 1 => q) (fun _ : Fin 1 => core) (fun _ => literal) (fun _ => stable)
    (fun _ => d) (0 : Fin 1)

include N in
theorem small_tract (small : ∀o : CurrentOccurrences.Id G (palette G base R),
    (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤2) :
    E.CurrentTract G (palette G base R) := by
  let marking : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
      (palette G base R).family R.final.ready.torsion := .bilinear N
  have hs := StableCurrentBinaryClosure.small_current_products G (palette G base R)
    R.final.ready.torsion marking basisB rfl
  have all : ∀o : CurrentOccurrences.Id G (palette G base R),
      leafPredicate G productClass basisB (CurrentOccurrences.savedLeaf G (palette G base R) o).1 :=
    fun o => hs.leaves o (small o)
  exact FrontierNativeClosure.relative_current_native_tractx G (palette G base R) .product basisB hs.edge
    ⟨fun o _ _ => all o,fun o _ _ => all o,fun o _ _ _ => all o,fun o _ _ _ => all o⟩

include noPrior N in
theorem dense_of_not_sparse_not_small (noSparse : ¬Sparse G base R)
    (large : ¬∀o : CurrentOccurrences.Id G (palette G base R),
      (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤2) : Dense G base R := by
  classical
  obtain ⟨o,ho⟩ := not_forall.mp large
  have nonbinary : 3≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by omega
  have even := R.final.ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G (palette G base R) o)
    (CurrentOccurrences.savedLeaf_prime G (palette G base R) o) nonbinary
  have proper : 4≤(CurrentOccurrences.savedLeaf G (palette G base R) o).1.1 := by
    rcases even with ⟨k,hk⟩
    omega
  obtain ⟨q,_path,four⟩ := GlobalCloseCompletionBDescent.quaternary_path_exists G base R noPrior N o proper
  have full : ∃p : Bool,BQ.FullParity G (Q.table G base four) p := by
    by_contra h
    exact noSparse ⟨q,four,h⟩
  exact ⟨q,four,full⟩

inductive Completion : Type 1 where
  | hard (proof : PaperControlledHardness.Original G)
  | tract (criterion : E.CurrentTract G (palette G base R))
  | ordinary (output : GlobalCloseCompletionBPrimeEq4.Output (C.mapped G (palette G base R)))
      (obstruction : StableHigherCurrentOrdinaryTerminal.Obstruction
        (preprocess (E.family G (palette G base R) output)))
  | dense (full : Dense G base R)

def complete : Completion G base R := Classical.choice (by
  classical
  by_cases sparse : Sparse G base R
  · rcases sparse_eq4_or_hard G base R noPrior N sparse with outputs | hard
    · obtain ⟨output⟩ := outputs
      rcases E.classified G (palette G base R) output with tract | negative
      · exact ⟨.tract tract⟩
      · exact ⟨.ordinary output negative⟩
    · exact ⟨.hard hard⟩
  · by_cases small : ∀o : CurrentOccurrences.Id G (palette G base R),
        (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1≤2
    · exact ⟨.tract (small_tract G base R N small)⟩
    · exact ⟨.dense (dense_of_not_sparse_not_small G base R noPrior N sparse small)⟩)

/-- Ordinary outputs carry the genuine whole-family squared-CSP programme;
its exact final oracle remains the original G input and answer encoding. -/
def Installed (c : Completion G base R) : Type 1 := match c with
  | .ordinary output _ => {p // p=E.squareCSPSource G (palette G base R) output}
  | _ => PUnit.{2}

def install (c : Completion G base R) : Installed G base R c := match c with
  | .ordinary output _ => ⟨E.squareCSPSource G (palette G base R) output,rfl⟩
  | .hard _ => PUnit.unit
  | .tract _ => PUnit.unit
  | .dense _ => PUnit.unit

structure Receipt : Type 1 where
  result : Completion G base R
  resultIdentity : result=complete G base R noPrior N
  installed : Installed G base R result

def produce : Receipt G base R noPrior N :=
  ⟨complete G base R noPrior N,rfl,install G base R _⟩

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Type 1 := match M with
  | .bilinear native => Receipt G base R noPrior native
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R noPrior M := by
  cases M with
  | bilinear native => exact produce G base R noPrior native
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | monomial => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 := match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted rfl (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) =>
      forMarking G base exhausted rfl (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def original_current_bilinear : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.BCurrent
end
