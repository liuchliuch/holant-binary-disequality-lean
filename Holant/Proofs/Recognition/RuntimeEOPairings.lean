import Holant.Proofs.Recognition.RuntimeTensorRowsSoundness
import Holant.Proofs.Tractability.EOEvaluation.EOConditionCertificate.Pairings

/-! Runtime oriented-perfect-pairing metadata. The same finite arity-generated
catalogue is checked for size-two blocks and full port coverage. Every accepted
raw packet reconstructs an actual oriented perfect pairing and every source
pairing has a generated accepted packet. No typed pairing is machine input.
This component is not an EO class-membership decision. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOPairings
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open UniformTensorWitnessBranch (Metadata metadataEncoding natListEncoding)
open RuntimeTensorRowsSoundness (ShapeData encodeShape reifiedShape)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def paired (m : Metadata) : Bool := m.1.all (fun k => decide (k=2))
def valid (n : ℕ) (m : Metadata) : Bool := RuntimeTensorValidation.valid (false,n,m) && paired m

theorem valid_correct (n : ℕ) (m : Metadata) : valid n m=true ↔
    RuntimeTensorValidation.valid (false,n,m)=true ∧ ∀i : Fin m.1.length,m.1.get i=2 := by
  simp only [valid,Bool.and_eq_true,paired,List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h.1,fun i => h.2 _ (List.get_mem m.1 i)⟩
  · intro h
    refine ⟨h.1,?_⟩
    intro k hk
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
    exact h.2 i

def boolFin : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i=1)
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

def slotEquiv {n : ℕ} (S : ShapeData n) (h : ∀i,S.2.1 i=2) :
    (Fin S.1 × Bool) ≃ (Σi : Fin S.1,Fin (S.2.1 i)) where
  toFun p := ⟨p.1,Fin.cast (h p.1).symm (boolFin p.2)⟩
  invFun p := (p.1,boolFin.symm (Fin.cast (h p.1) p.2))
  left_inv p := by rcases p with ⟨i,b⟩; simp
  right_inv p := by rcases p with ⟨i,j⟩; simp

def asPairing {n : ℕ} (S : ShapeData n) (h : ∀i,S.2.1 i=2) : OrientedPerfectPairing n :=
  ⟨S.1,(slotEquiv S h).trans S.2.2.1⟩

def pairing {n : ℕ} (m : Metadata) (hg : m∈RuntimeTensorCatalogue.catalogue n)
    (hv : valid n m=true) : OrientedPerfectPairing n :=
  asPairing (reifiedShape m hg false ((valid_correct n m).mp hv).1) ((valid_correct n m).mp hv).2

def sourcePorts {n : ℕ} (p : OrientedPerfectPairing n) : (Σ_ : Fin p.count,Fin 2) ≃ Fin n :=
  ((Equiv.sigmaEquivProd (Fin p.count) (Fin 2)).trans
    (Equiv.prodCongr (Equiv.refl (Fin p.count)) boolFin.symm)).trans p.ports

def sourceShape {n : ℕ} (p : OrientedPerfectPairing n) : ShapeData n :=
  ⟨p.count,(fun _ => 2),sourcePorts p,(fun _ => false)⟩
def source {n : ℕ} (p : OrientedPerfectPairing n) : Metadata := encodeShape (sourceShape p)

theorem source_mem {n : ℕ} (p : OrientedPerfectPairing n) : source p∈RuntimeTensorCatalogue.catalogue n := by
  have hn := Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.Pairings.twice_count p
  exact RuntimeTensorCatalogue.source_mem (fun _ : Fin p.count => 2) (sourcePorts p) (by omega) (fun _ => false)

theorem source_valid {n : ℕ} (p : OrientedPerfectPairing n) : valid n (source p)=true := by
  apply (valid_correct n (source p)).mpr
  constructor
  · exact RuntimeTensorValidation.source_valid false (fun _ : Fin p.count => 2) (sourcePorts p)
      (fun _ => false) (fun _ => by decide)
  · intro i
    change (List.ofFn (fun _ : Fin p.count => 2)).get i=2
    exact List.get_ofFn _ _

theorem asPairing_source {n : ℕ} (p : OrientedPerfectPairing n) :
    asPairing (sourceShape p) (fun _ => rfl)=p := by
  cases p with
  | mk c ports =>
    apply congrArg (OrientedPerfectPairing.mk c)
    apply Equiv.ext
    intro q
    rcases q with ⟨i,b⟩
    simp [asPairing,slotEquiv,sourceShape,sourcePorts]

theorem asPairing_congr {n : ℕ} (S T : ShapeData n) (he : S=T)
    (hS : ∀i,S.2.1 i=2) (hT : ∀i,T.2.1 i=2) : asPairing S hS=asPairing T hT := by
  subst T
  rfl

theorem source_roundtrip {n : ℕ} (p : OrientedPerfectPairing n) :
    pairing (source p) (source_mem p) (source_valid p)=p := by
  unfold pairing
  have hs := RuntimeTensorRowsSoundness.source_shape_roundtrip (sourceShape p) (source_mem p) false
    ((valid_correct n (source p)).mp (source_valid p)).1
  exact (asPairing_congr _ _ hs _ (fun _ => rfl)).trans (asPairing_source p)

abbrev encoding := pairEncoding encodingNatBool metadataEncoding

def pairedComputes : Computes metadataEncoding encodingBoolBool paired :=
  congrComputes (((Wiring.firstComputes natListEncoding (pairEncoding natListEncoding RuntimeTensorRows.wordEncoding)).andThen
    (WireLists.mapComputes encodingNatBool encodingBoolBool (fun k => decide (k=2))
      ((pairComputes (identityComputes encodingNatBool) (constantComputes encodingNatBool encodingNatBool 2)).andThen
        (equalComputes encodingNatBool)))).andThen ResidueCells.all)
      (fun m => by simp only [paired,List.all_map,Function.comp_def,id_eq])

def executes : Executes encoding encodingBoolBool (fun p => valid p.1 p.2) := by
  let p := Executes.ofComputes (identityComputes encoding)
  let f := Executes.ofComputes (constantComputes encoding encodingBoolBool false)
  let shape := (f.pair p).comp RuntimeTensorValidation.executes
  let pairs := Executes.ofComputes ((Wiring.secondComputes encodingNatBool metadataEncoding).andThen pairedComputes)
  exact (shape.pair pairs).comp (Executes.ofComputes
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun q => q.1 && q.2)))


/-- The physical finite list contains only checked pairings, and is generated
from binary n rather than supplied as padded catalogue data. -/
def catalogue (n : ℕ) : List Metadata := (RuntimeTensorCatalogue.catalogue n).filter (valid n)

theorem mem_catalogue (n : ℕ) (m : Metadata) : m∈catalogue n ↔
    m∈RuntimeTensorCatalogue.catalogue n ∧ valid n m=true := List.mem_filter

theorem source_catalogue {n : ℕ} (p : OrientedPerfectPairing n) : source p∈catalogue n :=
  (mem_catalogue n _).mpr ⟨source_mem p,source_valid p⟩

def singletonIf : Executes encoding RuntimeTensorCatalogue.catalogueEncoding
    (fun p => if valid p.1 p.2 then [p.2] else []) :=
  RuntimeTensorRows.choose _ _ executes
    ((RuntimeTensorRows.snd encodingNatBool metadataEncoding).comp
      (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton metadataEncoding)))
    (RuntimeTensorRows.const encoding RuntimeTensorCatalogue.catalogueEncoding [])

def catalogueExecutes : Executes encodingNatBool RuntimeTensorCatalogue.catalogueEncoding catalogue := by
  let raw := (NegativeCertificateMachine.Lists.map encodingNatBool metadataEncoding RuntimeTensorCatalogue.catalogueEncoding
    RuntimeTensorCatalogue.executes (fun n m => if valid n m then [m] else []) singletonIf).comp
      (Executes.ofComputes (WireLists.flatten metadataEncoding))
  exact raw.congr (fun n => by
    simp only [catalogue,←List.flatMap_def]
    induction RuntimeTensorCatalogue.catalogue n with
    | nil => rfl
    | cons m ms ih =>
      simp only [List.flatMap_cons,List.filter_cons]
      cases h : valid n m <;> simp [h,ih])

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOPairings
