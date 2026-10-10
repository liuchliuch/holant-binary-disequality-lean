import Holant.Proofs.Recognition.UniformTensorWitnessBranch
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineEnumerationValidity

/-!
# One runtime tensor metadata catalogue programme

Arity is a binary natural input, not a programme parameter. The actual list
controllers generate all bounded size lists, all length-n port-index lists,
and all length-n Boolean pivots. Completeness includes every bounded ordered
shape used by both existing tensor recognition branches. Candidates may be
invalid; no acceptance, partition validity, coefficient arithmetic, or full
varying-layout recognition theorem is claimed by this catalogue component.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorCatalogue
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open RootSearchDriver (cross mem_cross)
open UniformTensorWitnessBranch (Metadata metadata metadataEncoding natListEncoding)

abbrev catalogueEncoding := framedListEncoding metadataEncoding

def sizes (n : ℕ) : List (List ℕ) := StructuredCatalogue.lists (List.range (n+1)) n

def ports (n : ℕ) : List (List ℕ) := StructuralListMachine.exactLength (List.range n) n

def catalogue (n : ℕ) : List Metadata := cross (sizes n) (cross (ports n) (RationalTableMachine.words n))

theorem generated_bounds (n : ℕ) (m : Metadata) (hm : m ∈ catalogue n) :
    m.1.length≤n ∧ (∀k∈m.1,k≤n) ∧ m.2.1.length=n ∧
      (∀j∈m.2.1,j<n) ∧ m.2.2.length=n := by
  obtain ⟨hs,hrest⟩ := mem_cross.mp hm
  obtain ⟨hp,hb⟩ := mem_cross.mp hrest
  have hs' := RawAffineEnumerationValidity.lists_spec (List.range (n+1)) m.1 n hs
  have hp' := RawAffineEnumerationValidity.vector_spec (List.range n) n m.2.1 hp
  have hb' := RawAffineEnumerationValidity.vector_spec [false,true] n m.2.2 hb
  exact ⟨hs'.1,fun k hk => Nat.le_of_lt_succ (List.mem_range.mp (hs'.2 k hk)),hp'.1,
    fun j hj => List.mem_range.mp (hp'.2 j hj),hb'.1⟩

private theorem exactLength_mem {A : Type} (alphabet : List A) {n : ℕ} (xs : List A)
    (hlen : xs.length=n) (hm : ∀a∈xs,a∈alphabet) : xs ∈ StructuralListMachine.exactLength alphabet n := by
  subst n
  exact List.mem_map.mpr ⟨xs.get,FiniteBranchEnumeration.mem_vectors alphabet xs.get
    (fun i => hm _ (List.get_mem xs i)),List.ofFn_get xs⟩

theorem size_le {n count : ℕ} (arity : Fin count → ℕ)
    (e : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (i : Fin count) : arity i≤n := by
  have hi : Function.Injective (fun j : Fin (arity i) => e ⟨i,j⟩) := by
    intro j k h
    have h' := e.injective h
    exact (Sigma.mk.inj_iff.mp h').2 |> eq_of_heq
  simpa using Fintype.card_le_of_injective _ hi

theorem ports_length {n count : ℕ} (arity : Fin count → ℕ)
    (e : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) :
    ((List.finRange count).flatMap (fun i => (List.finRange (arity i)).map (fun j => (e ⟨i,j⟩).val))).length=n := by
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sigma,Fintype.card_fin] at hc
  simpa only [List.length_flatMap,List.length_map,List.length_finRange,List.length_ofFn,List.sum_ofFn,
    ←List.ofFn_eq_map] using hc

/-- Every bounded genuine shape occurs as literal generated metadata. This
proof does not choose which generated row will be accepted. -/
theorem source_mem {n count : ℕ} (arity : Fin count → ℕ)
    (e : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (hcount : count≤n) (pivot : Fin n → Bool) :
    metadata count arity e pivot ∈ catalogue n := by
  apply mem_cross.mpr
  constructor
  · apply RawAffineEnumeration.mem_lists
    · simpa using hcount
    · intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact List.mem_range.mpr (Nat.lt_succ_of_le (size_le arity e i))
  · apply mem_cross.mpr
    constructor
    · apply exactLength_mem
      · exact ports_length arity e
      · intro z hz
        obtain ⟨i,_,hz⟩ := List.mem_flatMap.mp hz
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
        exact List.mem_range.mpr (e ⟨i,j⟩).isLt
    · rw [RationalTableMachine.words_eq]
      exact List.mem_map.mpr ⟨pivot,SparseTransform.mem_allWords pivot,rfl⟩

theorem arity_shape_mem {n : ℕ} (S : TensorDecision.Shape n) (pivot : Fin n → Bool) :
    metadata S.count S.arity S.ports pivot ∈ catalogue n :=
  source_mem S.arity S.ports (Nat.le_of_lt_succ S.1.isLt) pivot

theorem matching_shape_mem {n : ℕ} (S : TensorDecisionStable.Shape n) (pivot : Fin n → Bool) :
    metadata S.count S.arity S.ports pivot ∈ catalogue n :=
  source_mem S.arity S.ports (Nat.le_of_lt_succ S.1.isLt) pivot

noncomputable section

def sizesExecutes : Executes encodingNatBool (framedListEncoding natListEncoding) sizes := by
  let alphabet := (Executes.ofComputes RationalInputMachine.Programs.successor).comp
    RationalInputMachine.Programs.range
  exact (alphabet.pair (Executes.ofComputes (identityComputes encodingNatBool))).comp
    (StructuralListMachine.boundedExecutes encodingNatBool)

def portsExecutes : Executes encodingNatBool (framedListEncoding natListEncoding) ports :=
  ((Executes.ofComputes (identityComputes encodingNatBool)).pair RationalInputMachine.Programs.range).comp
    (StructuralListMachine.exactExecutes encodingNatBool)

/-- Sole physical finite-control programme, independent of runtime n. -/
def executes : Executes encodingNatBool catalogueEncoding catalogue := by
  let tail := (portsExecutes.pair RationalTableMachine.wordsExecutes).comp
    (Executes.ofComputes (RootSearchDriver.crossComputes natListEncoding RationalTableMachine.wordEncoding))
  exact (sizesExecutes.pair tail).comp
    (Executes.ofComputes (RootSearchDriver.crossComputes natListEncoding
      (pairEncoding natListEncoding RationalTableMachine.wordEncoding)))

def source_outputs (n : ℕ) : TM2OutputsInTime executes.machine.computer
    (encodingNatBool.encode n) (some (catalogueEncoding.encode (catalogue n))) (executes.cost n) :=
  executes.outputs n

theorem primitive_bound (n : ℕ) :
    primitiveCost executes.machine (executes.outputs n).steps
      (some (initList executes.machine.computer (encodingNatBool.encode n)))≤
      executes.cost n*executes.machine.primitiveBudget := executes.primitive_bound n

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorCatalogue
