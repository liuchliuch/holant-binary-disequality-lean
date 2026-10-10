import Holant.Proofs.Closure.RetainedSingle
import Holant.Proofs.Closure.RetainedCatalogue
import Holant.Proofs.Closure.PhysicalPalette

/-! Additive exact prime-label installation from a genuine source PowerMacro.
All old whole trees are copied; only the new prime gets its literal leaf tree.
The existing factor-power machine is actually composed into both original-G
encodings. No direct realizability over the OLD palette is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent.PowerPalette
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (q : AnySignature (OI.K G)) (positive : 0 < q.1) (prime : Prime q)

abbrev count := P.count+1
abbrev arity := RetainedBranch.arity G P q
abbrev table := RetainedBranch.extended G P q

def oldLabel (i : Fin P.count) : Fin (count G P) := ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self P.count)⟩
def newLabel : Fin (count G P) := ⟨P.count,Nat.lt_succ_self P.count⟩

def trees (i : Fin (count G P)) :
    FactorTree (⟨arity G P q i.val,table G P q i⟩ : AnySignature (OI.K G)) :=
  if hi : i.val < P.count then
    RetainedCatalogue.transportTree (RetainedBranch.extended_old G P q ⟨i.val,hi⟩).symm (P.trees ⟨i.val,hi⟩)
  else
    RetainedCatalogue.transportTree (by
      have hn : i = newLabel G P := Fin.ext (by have := i.isLt; unfold count at this; dsimp [newLabel]; omega)
      rw [hn]
      exact (RetainedBranch.extended_new G P q).symm) (FactorTree.leaf q prime)

def occurrence (i : Fin (count G P)) : TreeOccurrence (OI.K G) :=
  ⟨⟨arity G P q i.val,table G P q i⟩,trees G P q prime i⟩

@[simp] theorem old_saved (i : Fin P.count) : occurrence G P q prime (oldLabel G P i) =
    (⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ : TreeOccurrence (OI.K G)) := by
  simp only [occurrence,trees,oldLabel,dif_pos i.isLt]
  exact RetainedCatalogue.transportTree_saved (L:=OI.K G) _ _
@[simp] theorem new_saved : occurrence G P q prime (newLabel G P) =
    (⟨q,FactorTree.leaf q prime⟩ : TreeOccurrence (OI.K G)) := by
  simp only [occurrence,trees,newLabel,dif_neg (Nat.lt_irrefl P.count)]
  exact RetainedCatalogue.transportTree_saved (L:=OI.K G) _ _

def family : SignatureFamily (OI.K G) := Set.range
  (fun i : Fin (count G P) => (⟨arity G P q i.val,table G P q i⟩ : AnySignature (OI.K G)))

include prime in
theorem old_retained (u : AnySignature (OI.K G)) (hu : u ∈ P.family) : u ∈ family G P q := by
  obtain ⟨i,rfl⟩ := hu
  exact ⟨oldLabel G P i,congrArg Sigma.fst (old_saved G P q prime i)⟩
include prime in
theorem new_retained : q ∈ family G P q :=
  ⟨newLabel G P,congrArg Sigma.fst (new_saved G P q prime)⟩

include positive in
theorem label_positive (i : Fin (count G P)) : 0 < arity G P q i.val := by
  by_cases hi : i.val < P.count
  · have h := RetainedBranch.extended_old G P q ⟨i.val,hi⟩
    have he : arity G P q i.val = P.arity i.val := congrArg Sigma.fst h
    rw [he]
    exact P.positive ⟨i.val,hi⟩
  · have hn : i = newLabel G P := Fin.ext (by have := i.isLt; unfold count at this; dsimp [newLabel]; omega)
    rw [hn]
    have he := congrArg Sigma.fst (RetainedBranch.extended_new G P q)
    change arity G P q P.count = q.1 at he
    change 0 < arity G P q P.count
    rw [he]
    exact positive

include prime in
theorem label_nonzero (i : Fin (count G P)) : table G P q i ≠ 0 := by
  by_cases hi : i.val < P.count
  · exact Eq.mpr (congrArg (fun z : AnySignature (OI.K G) => z.2 ≠ 0)
      (RetainedBranch.extended_old G P q ⟨i.val,hi⟩)) (P.nonzero ⟨i.val,hi⟩)
  · have hn : i = newLabel G P := Fin.ext (by have := i.isLt; unfold count at this; dsimp [newLabel]; omega)
    rw [hn]
    exact Eq.mpr (congrArg (fun z : AnySignature (OI.K G) => z.2 ≠ 0)
      (RetainedBranch.extended_new G P q)) prime.1

theorem leaves_retained (i : Fin (count G P)) (u : AnySignature (OI.K G))
    (hu : u ∈ (trees G P q prime i).leaves) : u ∈ family G P q := by
  by_cases hi : i.val < P.count
  · have hn : oldLabel G P ⟨i.val,hi⟩ = i := Fin.ext rfl
    rw [← hn] at hu
    have he := congrArg (fun z : TreeOccurrence (OI.K G) => z.2.leaves) (old_saved G P q prime ⟨i.val,hi⟩)
    change (trees G P q prime (oldLabel G P ⟨i.val,hi⟩)).leaves = (P.trees ⟨i.val,hi⟩).leaves at he
    rw [he] at hu
    exact old_retained G P q prime u (P.leavesRetained _ _ hu)
  · have hn : i = newLabel G P := Fin.ext (by have := i.isLt; unfold count at this; dsimp [newLabel]; omega)
    rw [hn] at hu
    have he := congrArg (fun z : TreeOccurrence (OI.K G) => z.2.leaves) (new_saved G P q prime)
    change (trees G P q prime (newLabel G P)).leaves = {q} at he
    rw [he] at hu
    have hq : u = q := Multiset.mem_singleton.mp hu
    exact hq ▸ new_retained G P q prime

def palette (M : GeneralPowerExposure.PowerMacro P.table q.2) : Palette G where
  count := count G P
  arity := arity G P q
  table := table G P q
  positive := label_positive G P q positive
  nonzero := label_nonzero G P q prime
  trees := trees G P q prime
  leavesRetained := leaves_retained G P q prime
  originalSaved i := by
    obtain ⟨j,hj⟩ := P.originalSaved i
    exact ⟨oldLabel G P j,(old_saved G P q prime j).trans hj⟩
  equality := old_retained G P q prime _ P.equality
  toOriginal := RetainedBranch.toOriginal G P q M
  fromOriginal := RetainedBranch.fromOriginal G P q

variable (M : GeneralPowerExposure.PowerMacro P.table q.2)
@[simp] theorem toOriginal_controlled : (palette G P q positive prime M).toOriginal.controlled =
    RetainedBranch.controlledToOriginal G P q M := rfl
@[simp] theorem fromOriginal_controlled : (palette G P q positive prime M).fromOriginal.controlled =
    RetainedBranch.controlledFromOriginal G P q := rfl

theorem retains_old : P.family ⊆ (palette G P q positive prime M).family :=
  old_retained G P q prime
theorem retains_new : q ∈ (palette G P q positive prime M).family := new_retained G P q prime

theorem saturated : FactorSaturated (palette G P q positive prime M).family :=
  Palette.saturated G _

def toOriginal_prefix_costs := Palette.toOriginal_prefix_costs G (palette G P q positive prime M)
def fromOriginal_prefix_costs := Palette.fromOriginal_prefix_costs G (palette G P q positive prime M)
def toOriginal_prefix_storage := Palette.toOriginal_prefix_storage G (palette G P q positive prime M)
def fromOriginal_prefix_storage := Palette.fromOriginal_prefix_storage G (palette G P q positive prime M)
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent.PowerPalette
