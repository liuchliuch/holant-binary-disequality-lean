import Holant.Proofs.Recognition.RuntimeEOViewSupport
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOView

/-! Runtime support for central and completed views is derived from the one
retained original K-inverse support table. Zero-by-mask entries need no new
algebraic search; other zero flags are read from the original word's stored
packet. This component consumes that checked table as an intermediate tape. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.Hardness
open CommonFieldMachine (Executes)
open RuntimeTensorRows (Word wordEncoding)
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable (Packet packetEncoding labelResultEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev ZeroRow := Word × Bool
abbrev zeroRowEncoding := pairEncoding wordEncoding encodingBoolBool
abbrev tableEncoding := framedListEncoding zeroRowEncoding
abbrev LookupInput := List Packet × Word
abbrev lookupEncoding := pairEncoding labelResultEncoding wordEncoding
abbrev Input := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.View × List Packet
abbrev encoding := pairEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding labelResultEncoding
abbrev cellEncoding := pairEncoding encoding wordEncoding

def lookupZero (r : LookupInput) : Bool := r.1.any (fun p => decide (p.1=r.2) && p.2.isSome)
def zero (r : Input) (w : Word) : Bool :=
  !(_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed (r.1,w)) || lookupZero (r.2,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.restricted (r.1,w))
def table (r : Input) : List ZeroRow := (RationalTableMachine.words (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity r.1)).map
  (fun w => (w,zero r w))

def lookupComputes : Computes lookupEncoding encodingBoolBool lookupZero := by
  let e := pairEncoding wordEncoding labelResultEncoding
  let test : Computes (pairEncoding wordEncoding packetEncoding) encodingBoolBool
      (fun p => decide (p.2.1=p.1) && p.2.2.isSome) := by
    let w := Wiring.firstComputes wordEncoding packetEncoding
    let p := Wiring.secondComputes wordEncoding packetEncoding
    let key := p.andThen (Wiring.firstComputes wordEncoding WitnessOutput.resultEncoding)
    let z := (p.andThen (Wiring.secondComputes wordEncoding WitnessOutput.resultEncoding)).andThen UniformTractXDecision.presence
    exact (pairComputes ((pairComputes key w).andThen (equalComputes wordEncoding)) z).andThen
      (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun q => q.1 && q.2))
  let swapped := pairComputes (Wiring.secondComputes labelResultEncoding wordEncoding)
    (Wiring.firstComputes labelResultEncoding wordEncoding)
  exact congrComputes (swapped.andThen ((mapListComputes wordEncoding packetEncoding encodingBoolBool
    (fun w p => decide (p.1=w) && p.2.isSome) test).andThen ResidueCells.any))
      (fun r => by simp only [lookupZero,List.any_map,Function.comp_def,id_eq])

def zeroExecutes : Executes cellEncoding encodingBoolBool (fun p => zero p.1 p.2) := by
  let r := RuntimeTensorRows.fst encoding wordEncoding
  let w := RuntimeTensorRows.snd encoding wordEncoding
  let v := r.comp (RuntimeTensorRows.fst _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding labelResultEncoding)
  let ps := r.comp (RuntimeTensorRows.snd _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding labelResultEncoding)
  let vw := v.pair w
  let mask := vw.comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowedExecutes
  let lookup := (ps.pair (vw.comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.restrictedExecutes)).comp (Executes.ofComputes lookupComputes)
  exact (mask.pair lookup).comp (Executes.ofComputes
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => !p.1 || p.2)))

def executes : Executes encoding tableEncoding table := by
  let arity := (Executes.ofComputes ((Wiring.firstComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding labelResultEncoding).andThen
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arityComputes)).comp RationalTableMachine.wordsExecutes
  let row := (RuntimeTensorRows.snd encoding wordEncoding).pair zeroExecutes
  exact NegativeCertificateMachine.Lists.map encoding wordEncoding zeroRowEncoding arity
    (fun r w => (w,zero r w)) row

theorem lookup_source (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (x : Fin (d.1.arity d.2) → Bool) :
    lookupZero (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelOutput d,List.ofFn x)=true ↔
      (d.1.G d.2) x=0 := by
  simp only [lookupZero,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelOutput,List.any_map,List.any_eq_true,Function.comp_def,
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.packet,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨w,hw,he,hz⟩
    subst w
    exact (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.source_zero_correct d x).mp hz
  · intro hx
    exact ⟨List.ofFn x,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.source_mem d x,rfl,
      (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.source_zero_correct d x).mpr hx⟩

theorem central_zero (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ) (x : Fin (d.1.arity d.2) → Bool) :
    zero ((d.1.arity d.2,false,k),_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelOutput d) (List.ofFn x)=true ↔
      Signature.centralRestriction ((d.1.G d.2)) x=0 := by
  simp only [zero,Bool.or_eq_true,Bool.not_eq_true_eq_eq_false,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.restricted_central,lookup_source]
  have hm := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed_central k x
  by_cases h : 2*Holant.weight x=d.1.arity d.2
  · have hb := hm.mpr h
    simp [hb,Signature.centralRestriction,h]
  · have hb : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((d.1.arity d.2,false,k),List.ofFn x)=false := by
      cases hh : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((d.1.arity d.2,false,k),List.ofFn x)
      · rfl
      · exact (h (hm.mp hh)).elim
    simp [hb,Signature.centralRestriction,h]

theorem completed_zero (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ)
    (x : Fin (d.1.arity d.2+SingleWeightCompletion.extra (d.1.arity d.2) k) → Bool) :
    zero ((d.1.arity d.2,true,k),_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelOutput d) (List.ofFn x)=true ↔
      SingleWeightCompletion.completed ((d.1.G d.2)) k x=0 := by
  simp only [zero,Bool.or_eq_true,Bool.not_eq_true_eq_eq_false,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.restricted_source,lookup_source]
  have hm := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed_completed k x
  by_cases h : SingleWeightCompletion.Pinned k x
  · have hb := hm.mpr h
    simp [hb,SingleWeightCompletion.completed_apply,h]
    rfl
  · have hb : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((d.1.arity d.2,true,k),List.ofFn x)=false := by
      cases hh : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.allowed ((d.1.arity d.2,true,k),List.ofFn x)
      · rfl
      · exact (h (hm.mp hh)).elim
    simp [hb,SingleWeightCompletion.completed_apply,h]

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport
