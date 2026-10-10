import Holant.Proofs.Traversal.ArityTwo.CycleProvider


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.SelectedProvider
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding PortWalk Descriptors
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)
variable (hd : ∀ i : Fin s, arity i.val ≤ 2)

def Good (x : RawRootReach.Input s b arity) : Prop :=
  degree (arity := arity) x.1.val x.2 = 1 ∨
    ∀ v, (x.1.val.graph x.1.property).label v = (x.1.val.graph x.1.property).label x.2 → degree (arity := arity) x.1.val v ≠ 1
abbrev Input := {x : RawRootReach.Input s b arity // Good s b arity x}
def encoding := RunComposition.restricted (RawRootReach.inputEncoding s b arity) (Good s b arity)

def unary (x : Input s b arity) : Option (UnaryProvider.Input s b arity) :=
  if h : degree (arity := arity) x.val.1.val x.val.2 = 1 then some ⟨x.val,h⟩ else none
def cycle (x : Input s b arity) : Option (CycleProvider.Input s b arity) :=
  if h : degree (arity := arity) x.val.1.val x.val.2 = 2 then
    some ⟨x.val,h,by rcases x.property with hu | hu; omega; exact hu⟩ else none
def scalar (x : Input s b arity) : Option (RawRootReach.Input s b arity) :=
  if degree (arity := arity) x.val.1.val x.val.2 = 0 then some x.val else none

def unaryComputes : Computes (encoding s b arity) (optionEncoding (UnaryProvider.encoding s b arity)) (unary s b arity) :=
  recode (RawBytecodeMachine.optionalComputes s b arity 1) Subtype.val (fun _ => rfl)
    (fun x => by by_cases h : degree (arity := arity) x.val.1.val x.val.2 = 1 <;>
      simp [RawBytecodeMachine.optional,RawBytecodeMachine.selectedDegree,unary,h,
        Frame.wordEncoding,optionEncoding,UnaryProvider.encoding,RunComposition.restricted])

def cycleComputes : Computes (encoding s b arity) (optionEncoding (CycleProvider.encoding s b arity)) (cycle s b arity) :=
  recode (RawBytecodeMachine.optionalComputes s b arity 2) Subtype.val (fun _ => rfl)
    (fun x => by by_cases h : degree (arity := arity) x.val.1.val x.val.2 = 2 <;>
      simp [RawBytecodeMachine.optional,RawBytecodeMachine.selectedDegree,cycle,h,
        Frame.wordEncoding,optionEncoding,CycleProvider.encoding,RunComposition.restricted])

def scalarComputes : Computes (encoding s b arity) (optionEncoding (RawRootReach.inputEncoding s b arity)) (scalar s b arity) :=
  recode (RawBytecodeMachine.optionalComputes s b arity 0) Subtype.val (fun _ => rfl)
    (fun x => by by_cases h : degree (arity := arity) x.val.1.val x.val.2 = 0 <;>
      simp [RawBytecodeMachine.optional,RawBytecodeMachine.selectedDegree,scalar,h,optionEncoding,Frame.wordEncoding])

def optionWord {X : Type} {e : Encoding X Bool} {f : X → Option (List Bool)}
    (w : Computes e (optionEncoding Frame.wordEncoding) f) :
    Computes e Frame.wordEncoding (fun x => (f x).getD []) :=
  congrComputes ((pairComputes w
    (constantComputes e (optionEncoding Frame.wordEncoding) none)).andThen
      (OptionChoice.computes [])) (fun _ => rfl)

def value (x : Input s b arity) :=
  ((scalar s b arity x).map (MatrixEmission.scalarWord s b arity labels codec)).getD [] ++
    ((unary s b arity x).map (UnaryProvider.value s b arity labels edges codec)).getD [] ++
    ((cycle s b arity x).map (CycleProvider.value s b arity labels edges codec)).getD []

def computes : Computes (encoding s b arity) Frame.wordEncoding (value s b arity labels edges codec) :=
  joinComputes (joinComputes
    (optionWord ((scalarComputes s b arity).andThen (OptionMap.computes (MatrixEmission.scalarComputes s b arity labels codec))))
    (optionWord ((unaryComputes s b arity).andThen (OptionMap.computes (UnaryProvider.computes s b arity labels edges codec hd)))))
    (optionWord ((cycleComputes s b arity).andThen (OptionMap.computes (CycleProvider.computes s b arity labels edges codec hd))))

theorem computes_machine : (computes s b arity labels edges codec hd).machine =
    RawBytecodeMachine.selectedComponentMachine s b arity labels edges codec := by
  simp only [computes, joinComputes, RunComposition.andThen_machine, pairComputes_machine,
    unaryComputes, cycleComputes, scalarComputes, recode, OptionMap.computes,
    UnaryProvider.computes_machine, CycleProvider.computes_machine, optionWord, congrComputes,
    identityComputes, constantComputes, OptionChoice.computes,
    RawBytecodeMachine.selectedComponentMachine, RawBytecodeMachine.optionalMachine,
    RawBytecodeMachine.optionValue, RawBytecodeMachine.join, WordJoin.computes,
    optionEncoding, Frame.wordEncoding, id_eq]

def Canonical (x : RawRootReach.Input s b arity) : Prop := (x.1.val.graph x.1.property).label x.2 = x.2
abbrev Root := {x : RawRootReach.Input s b arity // Canonical s b arity x}
def rootEncoding := RunComposition.restricted (RawRootReach.inputEncoding s b arity) (Canonical s b arity)

private theorem find_none_not {B : Type} (P : B → Bool) (xs : List B)
    (hx : xs.find? P = none) : ∀ x ∈ xs, P x = false := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    cases hp : P y with
    | true => simp [List.find?,hp] at hx
    | false =>
      intro x hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hp
      · exact ih (by simpa [List.find?,hp] using hx) x hm

theorem selected_good (x : Root s b arity) : Good s b arity (RawSeedSelection.value s b arity x.val) := by
  have hs := RawSeedSelection.selected_original s b arity x.val
  cases hf : ((x.val.1.val.graph x.val.1.property).componentVertices x.val.2).find?
      (fun v => decide (degree (arity := arity) x.val.1.val v = 1)) with
  | some v =>
    have hv : degree (arity := arity) x.val.1.val v = 1 := of_decide_eq_true (List.find?_some (p := fun v => decide (degree (arity := arity) x.val.1.val v = 1)) hf)
    have he : RawSeedSelection.selected s b arity x.val = v := by simpa [hf] using hs
    exact Or.inl (by simpa [RawSeedSelection.value,he] using hv)
  | none =>
    have he : RawSeedSelection.selected s b arity x.val = x.val.2 := by simpa [hf] using hs
    right
    intro v hv
    have hl : (x.val.1.val.graph x.val.1.property).label v = x.val.2 := by
      have hv' : (x.val.1.val.graph x.val.1.property).label v =
          (x.val.1.val.graph x.val.1.property).label x.val.2 := by
        simpa only [RawSeedSelection.value,he] using hv
      exact hv'.trans x.property
    have hm := ((x.val.1.val.graph x.val.1.property).mem_componentVertices x.val.2 v).mpr hl
    have hh := find_none_not _ _ hf v hm
    simpa only [decide_eq_false_iff_not,RawSeedSelection.value] using hh

def selected (x : Root s b arity) : Input s b arity :=
  ⟨RawSeedSelection.value s b arity x.val,selected_good s b arity x⟩

def selectComputes : Computes (rootEncoding s b arity) (encoding s b arity) (selected s b arity) :=
  recode (RawSeedSelection.computes s b arity) Subtype.val (fun _ => rfl) (fun _ => rfl)

def rootValue (x : Root s b arity) := value s b arity labels edges codec (selected s b arity x)
def rootComputes : Computes (rootEncoding s b arity) Frame.wordEncoding (rootValue s b arity labels edges codec) :=
  (selectComputes s b arity).andThen (computes s b arity labels edges codec hd)

theorem rootComputes_machine : (rootComputes s b arity labels edges codec hd).machine =
    RawBytecodeMachine.componentMachine s b arity labels edges codec := by
  simp only [rootComputes,RunComposition.andThen_machine,selectComputes,recode,
    computes_machine,RawBytecodeMachine.componentMachine]

include hd in
theorem rootValue_original (x : Root s b arity) :
    ∃ c, component x.val.1.val x.val.1.property
        (ActionTableMeaning.vertex x.val.1.val x.val.1.property labels)
        (ActionTableMeaning.edge x.val.1.val x.val.1.property edges) x.val.2 = some c ∧
      rootValue s b arity labels edges codec x = MatrixEmission.word codec c.code := by
  let y := selected s b arity x
  have hs := RawSeedSelection.selected_original s b arity x.val
  cases hf : ((x.val.1.val.graph x.val.1.property).componentVertices x.val.2).find?
      (fun v => decide (degree (arity := arity) x.val.1.val v = 1)) with
  | some v =>
    have hv : degree (arity := arity) x.val.1.val v = 1 := of_decide_eq_true (List.find?_some (p := fun v => decide (degree (arity := arity) x.val.1.val v = 1)) hf)
    have he : RawSeedSelection.selected s b arity x.val = v := by simpa [hf] using hs
    have hy : degree (arity := arity) y.val.1.val y.val.2 = 1 := by simpa [y,selected,RawSeedSelection.value,he] using hv
    obtain ⟨c,hc,hw⟩ := UnaryProvider.value_original s b arity labels edges codec hd ⟨y.val,hy⟩
    refine ⟨c,?_,?_⟩
    · simpa [component,hf,hv,UnaryProvider.vertex,UnaryProvider.edge,y,selected,RawSeedSelection.value,he] using hc
    · simpa [rootValue,value,scalar,unary,cycle,hy,y] using hw
  | none =>
    have he : RawSeedSelection.selected s b arity x.val = x.val.2 := by simpa [hf] using hs
    by_cases hz : degree (arity := arity) y.val.1.val y.val.2 = 0
    · refine ⟨.scalar (labels (y.val.1.val.signatureLabel y.val.1.property y.val.2) (fun _ => false)),?_,?_⟩
      · have hz' : degree (arity := arity) x.val.1.val x.val.2 = 0 := by
          simpa [y,selected,RawSeedSelection.value,he] using hz
        simp only [component,hf,if_pos hz',ActionTableMeaning.vertex]
        dsimp only [y,selected,RawSeedSelection.value]
        rw [he]
        rfl
      · simp [rootValue,value,scalar,unary,cycle,hz,MatrixEmission.scalarWord,sourceLabel,
          Component.code,y,RawClosedNetwork.signatureLabel]
    · have hn : degree (arity := arity) y.val.1.val y.val.2 ≠ 1 := by
        rcases y.property with hy | hy
        · have hh := find_none_not _ _ hf x.val.2
            (((x.val.1.val.graph x.val.1.property).mem_componentVertices x.val.2 x.val.2).mpr x.property)
          have hv : degree (arity := arity) x.val.1.val x.val.2 = 1 := by simpa [y,selected,RawSeedSelection.value,he] using hy
          simp [hv] at hh
        · exact hy _ rfl
      have hb : degree (arity := arity) y.val.1.val y.val.2 = 2 := by
        have hbound := hd (y.val.1.val.signatureLabel y.val.1.property y.val.2)
        change degree (arity := arity) y.val.1.val y.val.2 ≤ 2 at hbound
        omega
      have hp : CycleProvider.Property s b arity y.val :=
        ⟨hb,by rcases y.property with hy | hy; exact (hn hy).elim; exact hy⟩
      obtain ⟨c,hc,hw⟩ := CycleProvider.value_original s b arity labels edges codec hd ⟨y.val,hp⟩
      refine ⟨c,?_,?_⟩
      · have hb' : degree (arity := arity) x.val.1.val x.val.2 = 2 := by
          simpa only [y,selected,RawSeedSelection.value,he] using hb
        have hz' : degree (arity := arity) x.val.1.val x.val.2 ≠ 0 := by omega
        simpa only [component,hf,if_neg hz',dif_pos hb',CycleProvider.vertex,CycleProvider.edge,y,selected,RawSeedSelection.value,he] using hc
      · simpa [rootValue,value,scalar,unary,cycle,hb,y] using hw

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.SelectedProvider
