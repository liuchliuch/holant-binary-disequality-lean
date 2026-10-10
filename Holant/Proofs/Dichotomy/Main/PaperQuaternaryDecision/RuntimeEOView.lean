import Holant.Proofs.Recognition.RuntimeEOView
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeSupportFlags
import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.Reductions.SingleWeightCompletion.OrderedPins

/-! Runtime central/completed-table entry selection. The machine reads original
arity, central/completion mode, layer, and target word. It constructs the exact
appended-pin count, checks its literal pins, and emits the retained original
word plus a zero/nonzero mask. No transformed coefficients are inputs. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView
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
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev View := ℕ × (Bool × ℕ)
abbrev viewTailEncoding := pairEncoding encodingBoolBool encodingNatBool
abbrev viewEncoding := pairEncoding encodingNatBool viewTailEncoding
abbrev Input := View × Word
abbrev encoding := pairEncoding viewEncoding wordEncoding
abbrev selectionEncoding := pairEncoding encodingBoolBool wordEncoding

def arity (v : View) : ℕ := if v.2.1 then v.1+SingleWeightCompletion.extra v.1 v.2.2 else v.1
def restricted (r : Input) : Word := (List.range r.1.1).map (fun j => r.2.getD j false)
def pinned (r : Input) : Bool := (List.range (SingleWeightCompletion.extra r.1.1 r.1.2.2)).all
  (fun j => decide (r.2.getD (r.1.1+j) false=SingleWeightCompletion.pin r.1.1 r.1.2.2))
def central (r : Input) : Bool := decide (2*_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportFlags.wordWeight r.2=r.1.1)
def allowed (r : Input) : Bool := if r.1.2.1 then pinned r else central r
def selection (r : Input) : Bool × Word := (allowed r,restricted r)

abbrev natPairEncoding := pairEncoding encodingNatBool encodingNatBool

def extraComputes : Computes natPairEncoding encodingNatBool (fun p => SingleWeightCompletion.extra p.1 p.2) := by
  let n := Wiring.firstComputes encodingNatBool encodingNatBool
  let k := Wiring.secondComputes encodingNatBool encodingNatBool
  let double := (pairComputes k k).andThen RationalInputMachine.Programs.add
  let lhs := (pairComputes double n).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Endpoints.subtractComputes
  let rhs := (pairComputes n double).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Endpoints.subtractComputes
  exact congrComputes ((pairComputes lhs rhs).andThen RationalInputMachine.Programs.add) (fun p => by
    dsimp
    unfold SingleWeightCompletion.extra
    split_ifs <;> omega)

def pinComputes : Computes natPairEncoding encodingBoolBool (fun p => SingleWeightCompletion.pin p.1 p.2) := by
  let n := Wiring.firstComputes encodingNatBool encodingNatBool
  let k := Wiring.secondComputes encodingNatBool encodingNatBool
  let double := (pairComputes k k).andThen RationalInputMachine.Programs.add
  exact congrComputes ((pairComputes double n).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Endpoints.lessComputes)
      (fun p => by dsimp; simp only [SingleWeightCompletion.pin,two_mul])

def viewN := Wiring.firstComputes encodingNatBool viewTailEncoding
def viewTail := Wiring.secondComputes encodingNatBool viewTailEncoding
def viewMode := viewTail.andThen (Wiring.firstComputes encodingBoolBool encodingNatBool)
def viewLayer := viewTail.andThen (Wiring.secondComputes encodingBoolBool encodingNatBool)
def viewPair := pairComputes viewN viewLayer

def arityComputes : Computes viewEncoding encodingNatBool arity :=
  ifComputes viewMode ((pairComputes viewN (viewPair.andThen extraComputes)).andThen RationalInputMachine.Programs.add) viewN

def base := RuntimeTensorRows.fst viewEncoding wordEncoding
def word := RuntimeTensorRows.snd viewEncoding wordEncoding
def n := base.comp (Executes.ofComputes viewN)
def params := base.comp (Executes.ofComputes viewPair)

def restrictedExecutes : Executes encoding wordEncoding restricted := by
  let c := RuntimeTensorRows.fst encoding encodingNatBool
  let j := RuntimeTensorRows.snd encoding encodingNatBool
  exact NegativeCertificateMachine.Lists.map encoding encodingNatBool encodingBoolBool
    (n.comp RationalInputMachine.Programs.range) (fun r j => r.2.getD j false)
    (((c.comp word).pair j).comp (RuntimeTensorRows.lookup encodingBoolBool false))

def pinnedExecutes : Executes encoding encodingBoolBool pinned := by
  let c := RuntimeTensorRows.fst encoding encodingNatBool
  let j := RuntimeTensorRows.snd encoding encodingNatBool
  let index := ((c.comp n).pair j).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let value := ((c.comp word).pair index).comp (RuntimeTensorRows.lookup encodingBoolBool false)
  let target := (c.comp params).comp (Executes.ofComputes pinComputes)
  let test := (value.pair target).comp (Executes.ofComputes (equalComputes encodingBoolBool))
  let raw := (NegativeCertificateMachine.Lists.map encoding encodingNatBool encodingBoolBool
    ((params.comp (Executes.ofComputes extraComputes)).comp RationalInputMachine.Programs.range)
    (fun r j => decide (r.2.getD (r.1.1+j) false=SingleWeightCompletion.pin r.1.1 r.1.2.2)) test).comp
      (Executes.ofComputes ResidueCells.all)
  exact raw.congr (fun r => by simp only [pinned,List.all_map,Function.comp_def,id_eq])

def centralExecutes : Executes encoding encodingBoolBool central := by
  let weight := word.comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportFlags.weightExecutes
  let double := (weight.pair weight).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  exact ((double.pair n).comp (Executes.ofComputes (equalComputes encodingNatBool))).congr
    (fun r => by simp only [central]; congr 2 <;> omega)

def allowedExecutes : Executes encoding encodingBoolBool allowed :=
  RuntimeTensorRows.choose _ _ (base.comp (Executes.ofComputes viewMode)) pinnedExecutes centralExecutes

def executes : Executes encoding selectionEncoding selection := allowedExecutes.pair restrictedExecutes

theorem restricted_source {a b : ℕ} (complete : Bool) (k : ℕ) (x : Fin (a+b) → Bool) :
    restricted ((a,complete,k),List.ofFn x)=List.ofFn (fun j : Fin a => x (Fin.castAdd b j)) := by
  unfold restricted
  rw [RuntimeTensorRowsSoundness.map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  exact PositiveCertificateMachine.getD_ofFn x (Fin.castAdd b j) false

theorem restricted_central {a : ℕ} (k : ℕ) (x : Fin a → Bool) :
    restricted ((a,false,k),List.ofFn x)=List.ofFn x := by
  unfold restricted
  rw [RuntimeTensorRowsSoundness.map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  exact PositiveCertificateMachine.getD_ofFn x j false

theorem allowed_central {a : ℕ} (k : ℕ) (x : Fin a → Bool) :
    allowed ((a,false,k),List.ofFn x)=true ↔ 2*Holant.weight x=a := by
  simp only [allowed,central,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportFlags.wordWeight_source,Bool.false_eq_true,ite_false,decide_eq_true_eq]

theorem pinned_source {a : ℕ} (k : ℕ) (x : Fin (a+SingleWeightCompletion.extra a k) → Bool) :
    pinned ((a,true,k),List.ofFn x)=true ↔ SingleWeightCompletion.Pinned k x := by
  simp only [pinned,List.all_eq_true,List.mem_range,decide_eq_true_eq,SingleWeightCompletion.Pinned]
  constructor
  · intro h j
    have hh := h j.val j.isLt
    have he : (List.ofFn x).getD (a+j.val) false=x (Fin.natAdd a j) := by
      simpa only [Fin.val_natAdd,Nat.add_comm] using PositiveCertificateMachine.getD_ofFn x (Fin.natAdd a j) false
    exact he.symm.trans hh
  · intro h j hj
    have he : (List.ofFn x).getD (a+j) false=x (Fin.natAdd a ⟨j,hj⟩) := by
      simpa only [Fin.val_natAdd,Nat.add_comm] using PositiveCertificateMachine.getD_ofFn x (Fin.natAdd a ⟨j,hj⟩) false
    exact he.trans (h ⟨j,hj⟩)

theorem allowed_completed {a : ℕ} (k : ℕ) (x : Fin (a+SingleWeightCompletion.extra a k) → Bool) :
    allowed ((a,true,k),List.ofFn x)=true ↔ SingleWeightCompletion.Pinned k x :=
  pinned_source k x

theorem completed_value {K : Type*} [Field K] {a : ℕ} (f : Signature K a) (k : ℕ)
    (x : Fin (a+SingleWeightCompletion.extra a k) → Bool) :
    SingleWeightCompletion.completed f k x=
      if allowed ((a,true,k),List.ofFn x) then f (SingleWeightCompletion.restrict k x) else 0 := by
  rw [SingleWeightCompletion.completed_apply]
  simp only [allowed_completed]

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView
