import Holant.Proofs.Recognition.RuntimeTensorEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.StructuralChoicesMachine

/-! One finite programme generates all bounded completion profiles from the
runtime original family arities. The empty family yields the singleton empty
profile. Every emitted profile has exactly one layer in [0,arity] per original
label, and every bounded typed profile appears. No layers or padded catalogue
are supplied to the generator. This is enumeration, not EO acceptance. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOProfiles
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev Profile := List ℕ
abbrev profileEncoding := framedListEncoding encodingNatBool
abbrev outputEncoding := framedListEncoding profileEncoding

def choices (r : OriginalFamilyPackingMachine.Input) : List (List ℕ) :=
  r.1.map (fun v => List.range (v.1+1))
def profiles (r : OriginalFamilyPackingMachine.Input) : List Profile := StructuralChoicesMachine.product (choices r)

def choicesExecutes : Executes OriginalFamilyPackingMachine.encoding outputEncoding choices := by
  let family := Executes.ofComputes OriginalFamilyPackingMachine.family
  let vertex := (Executes.ofComputes (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding)).comp
    ((Executes.ofComputes RationalInputMachine.Programs.successor).comp RationalInputMachine.Programs.range)
  let cell := (RuntimeTensorRows.snd OriginalFamilyPackingMachine.encoding OriginalFamilyPackingMachine.vertexEncoding).comp vertex
  exact NegativeCertificateMachine.Lists.map OriginalFamilyPackingMachine.encoding OriginalFamilyPackingMachine.vertexEncoding
    profileEncoding family (fun _ v => List.range (v.1+1)) cell

def executes : Executes OriginalFamilyPackingMachine.encoding outputEncoding profiles :=
  choicesExecutes.comp (StructuralChoicesMachine.executes encodingNatBool)

variable {s : ℕ} (arity : Fin s → ℕ) (input : OriginalFamilyInput.Input arity)

theorem choices_source : choices (OriginalFamilyPackingSource.fromSource arity input false)=
    List.ofFn (fun i => List.range (arity i+1)) := by
  simp only [choices,OriginalFamilyPackingSource.fromSource,List.map_map,Function.comp_def,List.ofFn_eq_map]

theorem source_relation (p : Profile) (hp : p∈profiles (OriginalFamilyPackingSource.fromSource arity input false)) :
    List.Forall₂ (fun ks k => k∈ks) (List.ofFn (fun i => List.range (arity i+1))) p := by
  have h := (StructuralChoicesMachine.mem_product_iff _ _).mp hp
  rwa [choices_source] at h

theorem source_length (p : Profile) (hp : p∈profiles (OriginalFamilyPackingSource.fromSource arity input false)) :
    p.length=s := by
  simpa only [List.length_ofFn] using (source_relation arity input p hp).length_eq.symm

theorem source_bound (p : Profile) (hp : p∈profiles (OriginalFamilyPackingSource.fromSource arity input false))
    (i : Fin s) : p.getD i.val 0≤arity i := by
  have h := source_relation arity input p hp
  have hi : i.val<p.length := by rw [source_length arity input p hp]; exact i.isLt
  have hl : i.val<(List.ofFn (fun i => List.range (arity i+1))).length := by
    simpa only [List.length_ofFn] using i.isLt
  have hg := h.get hl hi
  have hh : p.getD i.val 0∈List.range (arity i+1) := by
    simpa only [List.getD_eq_getElem p 0 hi,List.get_eq_getElem,List.getElem_ofFn] using hg
  exact Nat.le_of_lt_succ (List.mem_range.mp hh)

def reify (p : Profile) (hp : p∈profiles (OriginalFamilyPackingSource.fromSource arity input false)) :
    (i : Fin s) → Fin (arity i+1) := fun i => ⟨p.getD i.val 0,Nat.lt_succ_of_le (source_bound arity input p hp i)⟩

theorem reify_exact (p : Profile) (hp : p∈profiles (OriginalFamilyPackingSource.fromSource arity input false)) :
    List.ofFn (fun i => (reify arity input p hp i).val)=p := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using (source_length arity input p hp).symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,reify]
    exact List.getD_eq_getElem p 0 hj'

theorem source_mem (p : (i : Fin s) → Fin (arity i+1)) :
    List.ofFn (fun i => (p i).val)∈profiles (OriginalFamilyPackingSource.fromSource arity input false) := by
  apply (StructuralChoicesMachine.mem_product_iff _ _).mpr
  rw [choices_source,List.ofFn_eq_map,List.ofFn_eq_map]
  have h : ∀is : List (Fin s),List.Forall₂ (fun ks k => k∈ks)
      (is.map (fun i => List.range (arity i+1))) (is.map (fun i => (p i).val)) := by
    intro is
    induction is with
    | nil => exact .nil
    | cons i is ih => exact .cons (List.mem_range.mpr (p i).isLt) ih
  exact h _

theorem empty_family (r : OriginalFamilyPackingMachine.Input) (h : r.1=[]) : profiles r=[[]] := by
  simp [profiles,choices,h,StructuralChoicesMachine.product]

def source_outputs : TM2OutputsInTime executes.machine.computer
    (OriginalFamilyPackingMachine.encoding.encode (OriginalFamilyPackingSource.fromSource arity input false))
    (some (outputEncoding.encode (profiles (OriginalFamilyPackingSource.fromSource arity input false))))
    (executes.cost (OriginalFamilyPackingSource.fromSource arity input false)) :=
  executes.outputs _

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOProfiles
