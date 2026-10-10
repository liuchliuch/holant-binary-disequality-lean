import Holant.Proofs.CountingMachines.StandardMachine.Support.Cost
import Mathlib.Computability.TuringMachine.StackTuringMachine

set_option backward.isDefEq.respectTransparency false
/-!
Adapted reference proof. See the task validation reports. The actual Mathlib stack-to-one-tape compiler, with the
original binary choice made ONLY at a normal source boundary. All go/return
movement is deterministic; a real tape halt has no successor. The source's
canonical held-halt edges are recorded separately as zero physical moves.

The finite label table is generated from the union of the original core and
alternate statement subterm supports. No simulation, accepted path, time
budget or accepting-control equation is a constructor input.

Mathlib's stack-to-tape theorem is an unclocked Reaches theorem. The statement
consumer below proves actual selected microsteps, using an internal normal
stopper so that one source guess cannot silently select another statement.
No polynomial tape-time theorem or ordinary TM0 #P equivalence is asserted.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TapeSimulation
open Turing Computability Holant.Complexity StateTransition Relation
open scoped BigOperators

variable (m : BinaryMachine)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k
local instance : Inhabited m.core.Λ := ⟨m.core.main⟩
local instance : Inhabited m.core.σ := ⟨m.core.initialState⟩

abbrev Alphabet := TM2to1.Γ' m.core.K m.core.Γ
abbrev Control := TM2to1.Λ' m.core.K m.core.Γ m.core.Λ m.core.σ
abbrev Cfg := TM1.Cfg (Alphabet m) (Control m) m.core.σ
abbrev Encoded := TM2to1.TrCfg (K := m.core.K) (Γ := m.core.Γ) (Λ := m.core.Λ) (σ := m.core.σ)
local instance : DecidableEq (Control m) := Classical.decEq _
noncomputable instance alphabetFinite : Fintype (Alphabet m) := inferInstance

def selected (b : Bool) : m.core.Λ → m.core.Stmt := if b then m.alternate else m.core.m
def program (b : Bool) : Control m → TM1.Stmt (Alphabet m) (Control m) m.core.σ :=
  TM2to1.tr (selected m b)

def split : Control m → Bool
  | .normal l => m.split l
  | .go _ _ _ => false
  | .ret _ => false

/-- Ordinary physical tape transitions stop at halt. None padding is NOT a
tape instruction, and every internal movement has only the None edge. -/
def step (token : Option Bool) (c : Cfg m) : Option (Cfg m) :=
  match c.l,token with
  | none,_ => none
  | some l,none => if split m l then none else some (TM1.stepAux (program m false l) c.var c.Tape)
  | some l,some b => if split m l then some (TM1.stepAux (program m b l) c.var c.Tape) else none

def boundary (c : Cfg m) : Prop :=
  match c.l with
  | none => True
  | some (.normal _) => True
  | _ => False

/-- Partial deterministic driver for exactly the interior of ONE source
statement. It stops at the next normal state, even when that state is a split. -/
def internalStep (c : Cfg m) : Option (Cfg m) :=
  match c.l with
  | some (.go _ _ _) => TM1.step (program m false) c
  | some (.ret _) => TM1.step (program m false) c
  | _ => none

theorem internal_no_choice (c d : Cfg m) (h : internalStep m c = some d) :
    step m none c = some d ∧ ∀ b, step m (some b) c = none := by
  rcases c with ⟨label,v,T⟩
  cases hc : label with
  | none => simp [internalStep,hc] at h
  | some l =>
    cases l with
    | normal l => simp [internalStep,hc] at h
    | go k a q =>
        constructor
        · simpa [internalStep,step,split,TM1.step,hc] using h
        · intro b; simp [step,split,hc]
    | ret q =>
        constructor
        · simpa [internalStep,step,split,TM1.step,hc] using h
        · intro b; simp [step,split,hc]

theorem real_halt (c : Cfg m) (hc : c.l = none) (token : Option Bool) : step m token c = none := by
  simp [step,hc]

theorem boundary_stops (c : Cfg m) (h : boundary m c) : internalStep m c = none := by
  cases hc : c.l with
  | none => simp [internalStep,hc]
  | some l => cases l <;> simp_all [boundary,internalStep]

private theorem supports_univ (q : m.core.Stmt) : TM2.SupportsStmt Finset.univ q := by
  induction q with
  | push k f q ih => exact ih
  | pop k f q ih => exact ih
  | peek k f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ihq ihr => exact ⟨ihq,ihr⟩
  | goto f => intro v; exact Finset.mem_univ _
  | halt => trivial

def support (b : Bool) : Finset (Control m) := TM2to1.trSupp (selected m b) Finset.univ
def controls : Finset (Control m) := support m false ∪ support m true

theorem normal_mem (b : Bool) (l : m.core.Λ) : TM2to1.Λ'.normal l ∈ support m b := by
  classical
  exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,Finset.mem_insert_self _ _⟩

private theorem compiled_support (b : Bool) : TM1.Supports (program m b) (support m b) :=
  TM2to1.tr_supports (selected m b) ⟨Finset.mem_univ _,fun l _ => supports_univ m (selected m b l)⟩

private theorem supports_mono {S T : Finset (Control m)} (h : S ⊆ T)
    (q : TM1.Stmt (Alphabet m) (Control m) m.core.σ) :
    TM1.SupportsStmt S q → TM1.SupportsStmt T q := by
  induction q with
  | move d q ih => exact ih
  | write f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ihq ihr => exact fun hs => ⟨ihq hs.1,ihr hs.2⟩
  | goto f => exact fun hs a v => h (hs a v)
  | halt => exact id

private theorem support_subset (b : Bool) : support m b ⊆ controls m := by
  cases b
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

/-- Both actual tables are closed in the SAME finite set. On internal go/ret
labels the core and alternate translated programs are literally identical. -/
theorem program_closed (b : Bool) (l : Control m) (hl : l ∈ controls m) :
    TM1.SupportsStmt (controls m) (program m b l) := by
  classical
  cases l with
  | normal l =>
      exact supports_mono m (support_subset m b) _ ((compiled_support m b).2 _ (normal_mem m b l))
  | go k a q =>
      rcases Finset.mem_union.mp hl with h | h
      · have hc := supports_mono m (support_subset m false) _ ((compiled_support m false).2 _ h)
        simpa only [program,TM2to1.tr] using hc
      · have hc := supports_mono m (support_subset m true) _ ((compiled_support m true).2 _ h)
        simpa only [program,TM2to1.tr] using hc
  | ret q =>
      rcases Finset.mem_union.mp hl with h | h
      · have hc := supports_mono m (support_subset m false) _ ((compiled_support m false).2 _ h)
        simpa only [program,TM2to1.tr] using hc
      · have hc := supports_mono m (support_subset m true) _ ((compiled_support m true).2 _ h)
        simpa only [program,TM2to1.tr] using hc

abbrev Label := {l : Control m // l ∈ controls m}
noncomputable instance : Fintype (Label m) := inferInstance

/-- Restrict the concrete goto table to its proved finite support. No
out-of-range fallback, rejecting flag or caller closure hypothesis is added. -/
def narrow (q : TM1.Stmt (Alphabet m) (Control m) m.core.σ)
    (h : TM1.SupportsStmt (controls m) q) : TM1.Stmt (Alphabet m) (Label m) m.core.σ :=
  match q with
  | .move d q => .move d (narrow q h)
  | .write f q => .write f (narrow q h)
  | .load f q => .load f (narrow q h)
  | .branch f q r => .branch f (narrow q h.1) (narrow r h.2)
  | .goto f => .goto (fun a v => ⟨f a v,h a v⟩)
  | .halt => .halt

def finiteProgram (b : Bool) (l : Label m) : TM1.Stmt (Alphabet m) (Label m) m.core.σ :=
  narrow m (program m b l.val) (program_closed m b l.val l.property)

def forget (c : TM1.Cfg (Alphabet m) (Label m) m.core.σ) : Cfg m :=
  ⟨c.l.map Subtype.val,c.var,c.Tape⟩

theorem narrow_stepAux (q : TM1.Stmt (Alphabet m) (Control m) m.core.σ)
    (h : TM1.SupportsStmt (controls m) q) (v : m.core.σ) (T : Tape (Alphabet m)) :
    forget m (TM1.stepAux (narrow m q h) v T) = TM1.stepAux q v T := by
  induction q generalizing v T with
  | move d q ih => exact ih h v (T.move d)
  | write f q ih => exact ih h v (T.write (f T.1 v))
  | load f q ih => exact ih h (f T.1 v) T
  | branch f q r ihq ihr =>
      cases hv : f T.1 v <;> simp only [narrow,TM1.stepAux,hv,Bool.cond_false,Bool.cond_true]
      · exact ihr h.2 v T
      · exact ihq h.1 v T
  | goto f => rfl
  | halt => rfl

/-- Actual finite one-tape tables, with finite alphabet and finite variable
store inherited from m. Rows are indexed by the concrete finite Label above. -/
structure Programme where
  core : Label m → TM1.Stmt (Alphabet m) (Label m) m.core.σ
  alternate : Label m → TM1.Stmt (Alphabet m) (Label m) m.core.σ
  choose : Label m → Bool
  main : Label m
  initialState : m.core.σ

def programme : Programme m where
  core := finiteProgram m false
  alternate := finiteProgram m true
  choose l := split m l.val
  main := ⟨.normal m.core.main,Finset.mem_union_left _ (normal_mem m false m.core.main)⟩
  initialState := m.core.initialState
local instance : Inhabited (Label m) := ⟨(programme m).main⟩

abbrev FiniteCfg := TM1.Cfg (Alphabet m) (Label m) m.core.σ
def finiteStep (token : Option Bool) (c : FiniteCfg m) : Option (FiniteCfg m) :=
  match c.l,token with
  | none,_ => none
  | some l,none => if (programme m).choose l then none
      else some (TM1.stepAux ((programme m).core l) c.var c.Tape)
  | some l,some b => if (programme m).choose l then
      some (TM1.stepAux (if b then (programme m).alternate l else (programme m).core l) c.var c.Tape)
      else none

theorem finite_step (token : Option Bool) (c : FiniteCfg m) :
    (finiteStep m token c).map (forget m) = step m token (forget m c) := by
  rcases c with ⟨l,v,T⟩
  cases l with
  | none => cases token <;> rfl
  | some l =>
      change (finiteStep m token ⟨some l,v,T⟩).map (forget m) =
        step m token ⟨some l.val,v,T⟩
      cases token with
      | none => cases hs : split m l.val <;>
          simp [finiteStep,programme,step,hs,finiteProgram,narrow_stepAux]
      | some b => cases b <;> cases hs : split m l.val <;>
          simp [finiteStep,programme,step,hs,finiteProgram,narrow_stepAux]

/-- The actual Mathlib single-move/single-write TM0 table for a selected
finite TM1 table. These two deterministic translations are NOT silently
identified as one nondeterministic TM0 dispatcher. -/
def opcodeMachine (bit : Bool) := TM1to0.tr (finiteProgram m bit)
def opcodeConfig (bit : Bool) (c : FiniteCfg m) := TM1to0.trCfg (finiteProgram m bit) c

private theorem finite_supports_univ
    (q : TM1.Stmt (Alphabet m) (Label m) m.core.σ) : TM1.SupportsStmt Finset.univ q := by
  induction q with
  | move d q ih => exact ih
  | write f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ihq ihr => exact ⟨ihq,ihr⟩
  | goto f => intro a v; exact Finset.mem_univ _
  | halt => trivial

theorem opcode_support (bit : Bool) :
    TM0.Supports (opcodeMachine m bit)
      ↑(TM1to0.trStmts (finiteProgram m bit) Finset.univ) :=
  TM1to0.tr_supports (finiteProgram m bit)
    ⟨Finset.mem_univ _,fun l _ => finite_supports_univ m (finiteProgram m bit l)⟩

/-- Genuine move/write microsteps for one selected row. The destination
configuration is the literal existing compiler image, not a free simulation
or a desired output premise. Its Reaches₁ receipt is still unclocked. -/
theorem row_opcodes (bit : Bool) (c d : FiniteCfg m)
    (h : TM1.step (finiteProgram m bit) c = some d) :
    Reaches₁ (TM0.step (opcodeMachine m bit)) (opcodeConfig m bit c) (opcodeConfig m bit d) := by
  have hr := TM1to0.tr_respects (finiteProgram m bit)
    (a₁ := c) (a₂ := opcodeConfig m bit c) rfl
  rw [h] at hr
  obtain ⟨next,he,ht⟩ := hr
  change Reaches₁ (TM0.step (opcodeMachine m bit)) (opcodeConfig m bit c) (TM1to0.trCfg (finiteProgram m bit) d)
  rw [he]
  exact ht

/-- This is only a proof driver: normal states stutter so its interior
Reaches proof can be shortened without introducing a second source choice. -/
def stay : m.core.Λ → m.core.Stmt := fun l => .goto (fun _ => l)
def stayingStep : Cfg m → Option (Cfg m) := TM1.step (TM2to1.tr (stay m))

theorem staying_to_internal (a b : Cfg m) (h : Reaches (stayingStep m) a b) :
    Reaches (internalStep m) a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail a b _ htail ih =>
      rcases a with ⟨label,v,T⟩
      cases label with
      | none => simp [stayingStep,TM1.step] at htail
      | some l =>
          cases l with
          | normal l =>
              have he : (⟨some (.normal l),v,T⟩ : Cfg m) = b :=
                Option.some.inj (by simpa [stayingStep,TM1.step,TM2to1.tr,stay,
                  TM2to1.trNormal,TM1.stepAux] using htail)
              exact he ▸ ih
          | go k action q =>
              exact ih.tail (by simpa [stayingStep,internalStep,program,TM2to1.tr,TM1.step] using htail)
          | ret q =>
              exact ih.tail (by simpa [stayingStep,internalStep,program,TM2to1.tr,TM1.step] using htail)

/-- Consume the actual Mathlib go/write/pop/return producers for one literal
source statement, with first normal state as an actual interior stopping point. -/
theorem statement_simulates (q : m.core.Stmt) (v : m.core.σ) (S : ∀ k, List (m.core.Γ k))
    (L : ListBlank (∀ k, Option (m.core.Γ k)))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    ∃ b : Cfg m, Encoded m (TM2.stepAux q v S) b ∧
      Reaches (internalStep m) (TM1.stepAux (TM2to1.trNormal q) v (Tape.mk' ∅ (TM2to1.addBottom L))) b := by
  have h : ∃ b : Cfg m, Encoded m (TM2.stepAux q v S) b ∧
      Reaches (stayingStep m) (TM1.stepAux (TM2to1.trNormal q) v (Tape.mk' ∅ (TM2to1.addBottom L))) b := by
    induction q using TM2to1.stmtStRec generalizing v S L hL with
    | run k action q ih => exact TM2to1.tr_respects_aux (stay m) hL action @ih
    | load f q ih => exact ih (f v) S L hL
    | branch f q r ihq ihr =>
        cases hf : f v
        · simpa only [TM2.stepAux,TM2to1.trNormal,TM1.stepAux,hf,Bool.cond_false] using ihr v S L hL
        · simpa only [TM2.stepAux,TM2to1.trNormal,TM1.stepAux,hf,Bool.cond_true] using ihq v S L hL
    | goto f => exact ⟨_,TM2to1.TrCfg.mk L hL,ReflTransGen.refl⟩
    | halt => exact ⟨_,TM2to1.TrCfg.mk L hL,ReflTransGen.refl⟩
  obtain ⟨b,hb,hr⟩ := h
  exact ⟨b,hb,staying_to_internal m _ _ hr⟩

theorem encoded_boundary (c : m.Config) (b : Cfg m) (h : Encoded m c b) : boundary m b := by
  cases h with
  | @mk q v S L hL => cases q <;> trivial

theorem encoded_label (c : m.Config) (a : Cfg m) (h : Encoded m c a) :
    c.l.map TM2to1.Λ'.normal = a.l := by cases h; rfl

theorem encoded_state (c : m.Config) (a : Cfg m) (h : Encoded m c a) :
    c.var = a.var := by cases h; rfl

/-- Read the original exact finite stack from the actual marked tape. The
ListBlank quotient cannot erase a source symbol, since source rows are some. -/
theorem encoded_stack (c : m.Config) (a : Cfg m) (h : Encoded m c a)
    (k : m.core.K) (n : ℕ) :
    (c.stk k).reverse[n]? = ((a.Tape.right₀).nth n).2 k := by
  cases h with
  | mk L hL =>
      rw [Tape.mk'_right₀,TM2to1.addBottom_nth_snd]
      exact (TM2to1.stk_nth_val n (hL k)).symm

theorem encoded_left_unique (c d : m.Config) (a : Cfg m)
    (hc : Encoded m c a) (hd : Encoded m d a) : c = d := by
  have hl : c.l = d.l := by
    have he := (encoded_label m c a hc).trans (encoded_label m d a hd).symm
    cases hcl : c.l <;> cases hdl : d.l <;> simp_all
  have hv : c.var = d.var := (encoded_state m c a hc).trans (encoded_state m d a hd).symm
  have hS : c.stk = d.stk := by
    funext k
    apply List.reverse_injective
    apply List.ext_getElem?
    intro n
    exact (encoded_stack m c a hc k n).trans (encoded_stack m d a hd k n).symm
  cases c
  cases d
  cases hl
  cases hv
  cases hS
  rfl

theorem encoded_right_unique (c : m.Config) (a b : Cfg m)
    (ha : Encoded m c a) (hb : Encoded m c b) : a = b := by
  cases ha with
  | mk L hL =>
      cases hb with
      | mk L' hL' =>
          have he : L = L' := by
            apply ListBlank.ext
            intro n
            funext k
            exact (TM2to1.stk_nth_val n (hL k)).trans (TM2to1.stk_nth_val n (hL' k)).symm
          subst L'
          rfl

theorem encoded_left_blank (c : m.Config) (a : Cfg m) (h : Encoded m c a) : a.Tape.left = ∅ := by
  cases h; rfl

/-- Actual boundary tape storage: the bottom marker is at cell zero and all
other cells beyond the original proved stack capacity are exactly blank. -/
theorem encoded_cells (c : m.Config) (a : Cfg m) (h : Encoded m c a) (B : ℕ)
    (hB : ∀ k, (c.stk k).length ≤ B) (n : ℕ) (hn : B+1 ≤ n) :
    (a.Tape.right₀).nth n = default := by
  cases h with
  | @mk q v S L hL =>
      cases n with
      | zero => omega
      | succ n =>
          rw [Tape.mk'_right₀]
          apply Prod.ext
          · exact TM2to1.addBottom_nth_succ_fst L n
          · funext k
            rw [TM2to1.addBottom_nth_snd,TM2to1.stk_nth_val _ (hL k)]
            exact List.getElem?_eq_none (by simp only [List.length_reverse]; have hk : (S k).length ≤ B := hB k; omega)

theorem internal_endpoint_unique (a b c : Cfg m)
    (hab : Reaches (internalStep m) a b) (hac : Reaches (internalStep m) a c)
    (hb : boundary m b) (hc : boundary m c) : b = c :=
  Part.mem_unique (StateTransition.mem_eval.mpr ⟨hab,boundary_stops m b hb⟩)
    (StateTransition.mem_eval.mpr ⟨hac,boundary_stops m c hc⟩)

/-- One actual source-labelled tape step, then only actual deterministic None
steps until its next boundary. A held source halt has ZERO tape operations. -/
inductive Macro (token : Option Bool) (a b : Cfg m) : Prop
  | real (first : Cfg m) : step m token a = some first →
      Reaches (internalStep m) first b → boundary m b → Macro token a b
  | padding : a.l = none → token = none → a = b → Macro token a b

theorem macro_endpoint_unique (token : Option Bool) (a b c : Cfg m)
    (hb : Macro m token a b) (hc : Macro m token a c) : b = c := by
  cases hb with
  | real first hf hr hboundary =>
      cases hc with
      | real next hg hs hbound =>
          have he : first = next := Option.some.inj (hf.symm.trans hg)
          subst next
          exact internal_endpoint_unique m first b c hr hs hboundary hbound
      | padding hh _ _ => simp [step,hh] at hf
  | padding hh _ he =>
      cases hc with
      | real next hg _ _ => simp [step,hh] at hg
      | padding _ _ hf => exact he.symm.trans hf

/-- Active original steps are physically simulated with their SAME token.
The original state/stack equation determines the resulting tape state. -/
theorem simulates (token : Option Bool) (c d : m.Config) (a : Cfg m)
    (hc : c.l.isSome = true) (h : m.step token c = some d) (ha : Encoded m c a) :
    ∃ b : Cfg m, Encoded m d b ∧ Macro m token a b := by
  cases ha with
  | @mk l v S L hL =>
      cases l with
      | none => simp at hc
      | some l =>
          have chosen (bit : Bool) (hq : TM2.stepAux (selected m bit l) v S = d)
              (ht : step m token
                ⟨some (.normal l),v,Tape.mk' ∅ (TM2to1.addBottom L)⟩ =
                  some (TM1.stepAux (TM2to1.trNormal (selected m bit l)) v
                    (Tape.mk' ∅ (TM2to1.addBottom L)))) :
              ∃ b : Cfg m, Encoded m d b ∧ Macro m token
                ⟨some (.normal l),v,Tape.mk' ∅ (TM2to1.addBottom L)⟩ b := by
            obtain ⟨b,hb,hr⟩ := statement_simulates m (selected m bit l) v S L hL
            rw [hq] at hb
            exact ⟨b,hb,Macro.real _ ht hr (encoded_boundary m _ _ hb)⟩
          cases token with
          | none =>
              cases hs : m.split l with
              | true => simp [BinaryMachine.step,hs] at h
              | false =>
                  apply chosen false (Option.some.inj (by simpa [BinaryMachine.step,selected,hs,ite_apply] using h))
                  simp [step,split,program,TM2to1.tr,hs]
          | some bit =>
              cases hs : m.split l with
              | false => simp [BinaryMachine.step,hs] at h
              | true =>
                  apply chosen bit (Option.some.inj (by simpa [BinaryMachine.step,selected,hs,ite_apply] using h))
                  simp [step,split,program,TM2to1.tr,hs]

theorem simulates_held (token : Option Bool) (c d : m.Config) (a : Cfg m)
    (h : m.step token c = some d) (ha : Encoded m c a) :
    ∃ b : Cfg m, Encoded m d b ∧ Macro m token a b := by
  cases hl : c.l with
  | some l => exact simulates m token c d a (by simp [hl]) h ha
  | none =>
      cases token with
      | some bit => simp [BinaryMachine.step,hl] at h
      | none =>
          have hd : c = d := Option.some.inj (by simpa [BinaryMachine.step,hl] using h)
          subst d
          have hal : a.l = none := by
            have he := encoded_label m c a ha
            simpa only [hl,Option.map_none] using he.symm
          exact ⟨a,ha,Macro.padding hal rfl rfl⟩

/-- A physical macro beginning at an encoded source boundary cannot invent
an edge: the only allowed token is exactly the original split/deterministic
token, including the sole None record at an already halted source. -/
theorem macro_source_step (token : Option Bool) (c : m.Config) (a b : Cfg m)
    (ha : Encoded m c a) (h : Macro m token a b) :
    ∃ d : m.Config, m.step token c = some d := by
  cases ha with
  | @mk l v S L hL =>
      cases l with
      | none =>
          cases token with
          | none => exact ⟨_,rfl⟩
          | some bit =>
              cases h with
              | real first ht _ _ => simp [step] at ht
              | padding _ ht _ => cases ht
      | some l =>
          cases token with
          | none =>
              cases hs : m.split l with
              | false => exact ⟨TM2.stepAux (m.core.m l) v S,by simp [BinaryMachine.step,hs]⟩
              | true =>
                  cases h with
                  | real first ht _ _ => simp [step,split,hs] at ht
                  | padding hh _ _ => cases hh
          | some bit =>
              cases hs : m.split l with
              | true => exact ⟨TM2.stepAux (if bit then m.alternate l else m.core.m l) v S,by simp [BinaryMachine.step,hs]⟩
              | false =>
                  cases h with
                  | real first ht _ _ => simp [step,split,hs] at ht
                  | padding hh _ _ => cases hh

theorem reflects (token : Option Bool) (c : m.Config) (a b : Cfg m)
    (ha : Encoded m c a) (h : Macro m token a b) :
    ∃ d : m.Config, m.step token c = some d ∧ Encoded m d b := by
  obtain ⟨d,hd⟩ := macro_source_step m token c a b ha h
  obtain ⟨b',he,hmacro⟩ := simulates_held m token c d a hd ha
  have hb : b' = b := macro_endpoint_unique m token a b' b hmacro h
  exact ⟨d,hd,hb ▸ he⟩

def Trace : List (Option Bool) → Cfg m → Cfg m → Prop
  | [],a,b => a = b
  | token::tokens,a,b => ∃ next, Macro m token a next ∧ Trace tokens next b

theorem trace_simulates (tokens : List (Option Bool)) (c d : m.Config) (a : Cfg m)
    (h : m.TraceValid tokens c d) (ha : Encoded m c a) :
    ∃ b : Cfg m, Encoded m d b ∧ Trace m tokens a b := by
  induction tokens generalizing c a with
  | nil => change c = d at h; subst d; exact ⟨a,ha,rfl⟩
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := h
      obtain ⟨mid,hm,ht⟩ := simulates_held m token c next a hs ha
      obtain ⟨b,hb,htrace⟩ := ih next mid hr hm
      exact ⟨b,hb,mid,ht,htrace⟩

theorem trace_reflects (tokens : List (Option Bool)) (c : m.Config) (a b : Cfg m)
    (ha : Encoded m c a) (h : Trace m tokens a b) :
    ∃ d : m.Config, m.TraceValid tokens c d ∧ Encoded m d b := by
  induction tokens generalizing c a with
  | nil =>
      change a = b at h
      exact ⟨c,rfl,h ▸ ha⟩
  | cons token tokens ih =>
      obtain ⟨mid,hstep,hrest⟩ := h
      obtain ⟨next,hs,he⟩ := reflects m token c a mid ha hstep
      obtain ⟨d,hr,hd⟩ := ih next mid he hrest
      exact ⟨d,⟨next,hs,hr⟩,hd⟩

theorem trace_iff (tokens : List (Option Bool)) (c d : m.Config) (a b : Cfg m)
    (ha : Encoded m c a) (hb : Encoded m d b) :
    Trace m tokens a b ↔ m.TraceValid tokens c d := by
  constructor
  · intro h
    obtain ⟨d',hr,hd⟩ := trace_reflects m tokens c a b ha h
    exact encoded_left_unique m d' d b hd hb ▸ hr
  · intro h
    obtain ⟨b',he,hr⟩ := trace_simulates m tokens c d a h ha
    exact encoded_right_unique m d b' b he hb ▸ hr

def finiteInternalStep (c : FiniteCfg m) : Option (FiniteCfg m) :=
  match c.l with
  | some l => match l.val with
    | .go _ _ _ => finiteStep m none c
    | .ret _ => finiteStep m none c
    | .normal _ => none
  | none => none

theorem finite_internal_step (c : FiniteCfg m) :
    (finiteInternalStep m c).map (forget m) = internalStep m (forget m c) := by
  cases hl : c.l with
  | none => simp [finiteInternalStep,internalStep,forget,hl]
  | some l =>
      cases hv : l.val with
      | normal label => simp [finiteInternalStep,internalStep,forget,hl,hv]
      | go k action q =>
          simpa [finiteInternalStep,internalStep,forget,hl,hv,step,split,TM1.step]
            using finite_step m none c
      | ret q =>
          simpa [finiteInternalStep,internalStep,forget,hl,hv,step,split,TM1.step]
            using finite_step m none c

theorem finite_step_lift (token : Option Bool) (a : FiniteCfg m) (b : Cfg m)
    (h : step m token (forget m a) = some b) :
    ∃ c : FiniteCfg m, finiteStep m token a = some c ∧ forget m c = b := by
  have he := finite_step m token a
  cases hs : finiteStep m token a with
  | none => simp [hs,h] at he
  | some c =>
      exact ⟨c,rfl,Option.some.inj (by simpa only [hs,Option.map_some,h] using he)⟩

theorem finite_internal_lift (a : FiniteCfg m) (b : Cfg m)
    (h : internalStep m (forget m a) = some b) :
    ∃ c : FiniteCfg m, finiteInternalStep m a = some c ∧ forget m c = b := by
  have he := finite_internal_step m a
  cases hs : finiteInternalStep m a with
  | none => simp [hs,h] at he
  | some c =>
      exact ⟨c,rfl,Option.some.inj (by simpa only [hs,Option.map_some,h] using he)⟩

theorem finite_reaches_forget (a b : FiniteCfg m)
    (h : Reaches (finiteInternalStep m) a b) :
    Reaches (internalStep m) (forget m a) (forget m b) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail c d _ hcd ih =>
      apply ih.tail
      change internalStep m (forget m c) = some (forget m d)
      rw [← finite_internal_step,hcd]
      rfl

theorem finite_reaches_lift (a : FiniteCfg m) (b : Cfg m)
    (h : Reaches (internalStep m) (forget m a) b) :
    ∃ c : FiniteCfg m, forget m c = b ∧ Reaches (finiteInternalStep m) a c := by
  induction h with
  | refl => exact ⟨a,rfl,ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
      obtain ⟨c',hc,hr⟩ := ih
      obtain ⟨d',hs,hd⟩ := finite_internal_lift m c' d (hc.symm ▸ hcd)
      exact ⟨d',hd,hr.tail hs⟩

/-- Same physical first edge and deterministic interior, now entirely on the
finite label subtype and its actual narrowed syntax tables. -/
inductive FiniteMacro (token : Option Bool) (a b : FiniteCfg m) : Prop
  | real (first : FiniteCfg m) : finiteStep m token a = some first →
      Reaches (finiteInternalStep m) first b → boundary m (forget m b) → FiniteMacro token a b
  | padding : a.l = none → token = none → a = b → FiniteMacro token a b

theorem finite_macro_forget (token : Option Bool) (a b : FiniteCfg m)
    (h : FiniteMacro m token a b) : Macro m token (forget m a) (forget m b) := by
  cases h with
  | real first hf hr hb =>
      apply Macro.real (forget m first)
      · rw [← finite_step,hf]; rfl
      · exact finite_reaches_forget m first b hr
      · exact hb
  | padding hh ht he => exact Macro.padding (by simp [forget,hh]) ht (congrArg (forget m) he)

theorem finite_macro_lift (token : Option Bool) (a : FiniteCfg m) (b : Cfg m)
    (h : Macro m token (forget m a) b) :
    ∃ c : FiniteCfg m, forget m c = b ∧ FiniteMacro m token a c := by
  cases h with
  | real first hf hr hb =>
      obtain ⟨first',hf',he⟩ := finite_step_lift m token a first hf
      obtain ⟨b',hb',hr'⟩ := finite_reaches_lift m first' b (he.symm ▸ hr)
      exact ⟨b',hb',FiniteMacro.real first' hf' hr' (hb'.symm ▸ hb)⟩
  | padding hh ht he =>
      have hal : a.l = none := by
        cases hl : a.l with
        | none => rfl
        | some l => simp [forget,hl] at hh
      exact ⟨a,he,FiniteMacro.padding hal ht rfl⟩

def FiniteTrace : List (Option Bool) → FiniteCfg m → FiniteCfg m → Prop
  | [],a,b => a = b
  | token::tokens,a,b => ∃ next, FiniteMacro m token a next ∧ FiniteTrace tokens next b

theorem finite_trace_forget (tokens : List (Option Bool)) (a b : FiniteCfg m)
    (h : FiniteTrace m tokens a b) : Trace m tokens (forget m a) (forget m b) := by
  induction tokens generalizing a with
  | nil => exact congrArg (forget m) h
  | cons token tokens ih =>
      obtain ⟨mid,hs,hr⟩ := h
      exact ⟨forget m mid,finite_macro_forget m token a mid hs,ih mid hr⟩

theorem finite_trace_lift (tokens : List (Option Bool)) (a : FiniteCfg m) (b : Cfg m)
    (h : Trace m tokens (forget m a) b) :
    ∃ c : FiniteCfg m, forget m c = b ∧ FiniteTrace m tokens a c := by
  induction tokens generalizing a with
  | nil => exact ⟨a,h,rfl⟩
  | cons token tokens ih =>
      obtain ⟨mid,hs,hr⟩ := h
      obtain ⟨mid',he,hs'⟩ := finite_macro_lift m token a mid hs
      obtain ⟨b',hb,hr'⟩ := ih mid' (he.symm ▸ hr)
      exact ⟨b',hb,mid',hs',hr'⟩

theorem finite_internal_no_choice (a b : FiniteCfg m)
    (h : finiteInternalStep m a = some b) :
    finiteStep m none a = some b ∧ ∀ bit, finiteStep m (some bit) a = none := by
  cases hl : a.l with
  | none => simp [finiteInternalStep,hl] at h
  | some l =>
      cases hv : l.val with
      | normal label => simp [finiteInternalStep,hl,hv] at h
      | go k action q =>
          constructor
          · simpa only [finiteInternalStep,hl,hv] using h
          · intro bit; simp [finiteStep,programme,split,hl,hv]
      | ret q =>
          constructor
          · simpa only [finiteInternalStep,hl,hv] using h
          · intro bit; simp [finiteStep,programme,split,hl,hv]

/-- Literal one-tape row execution: unlike FiniteTrace, each list element
here performs exactly one actual TM1 statement-table row. No held edges. -/
def InstructionTrace : List (Option Bool) → FiniteCfg m → FiniteCfg m → Prop
  | [],a,b => a = b
  | token::tokens,a,b => ∃ next, finiteStep m token a = some next ∧ InstructionTrace tokens next b

theorem instruction_append (left right : List (Option Bool)) (a b c : FiniteCfg m)
    (hl : InstructionTrace m left a b) (hr : InstructionTrace m right b c) :
    InstructionTrace m (left++right) a c := by
  induction left generalizing a with
  | nil => subst a; exact hr
  | cons token tokens ih =>
      obtain ⟨mid,hs,ht⟩ := hl
      exact ⟨mid,hs,ih mid ht⟩

/-- Extract a finite, exact sequence of actual None rows from the Mathlib
Reaches producer. n is produced by its proof, never supplied as a free clock. -/
theorem internal_instructions (a b : FiniteCfg m)
    (h : Reaches (finiteInternalStep m) a b) :
    ∃ n : ℕ, InstructionTrace m (List.replicate n none) a b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | @tail c d _ hcd ih =>
      obtain ⟨n,hn⟩ := ih
      refine ⟨n+1,?_⟩
      rw [List.replicate_succ']
      exact instruction_append m _ _ a c d hn
        ⟨d,(finite_internal_no_choice m c d hcd).1,rfl⟩

theorem finite_macro_instructions (token : Option Bool) (a b : FiniteCfg m)
    (h : FiniteMacro m token a b) :
    ∃ instructions : List (Option Bool), InstructionTrace m instructions a b ∧
      instructions.filterMap id = token.toList := by
  cases h with
  | real first hf hr _ =>
      obtain ⟨n,hn⟩ := internal_instructions m first b hr
      refine ⟨token :: List.replicate n none,⟨first,hf,hn⟩,?_⟩
      cases token <;> simp
  | padding _ ht he =>
      subst token
      exact ⟨[],he,rfl⟩

theorem finite_trace_instructions (tokens : List (Option Bool)) (a b : FiniteCfg m)
    (h : FiniteTrace m tokens a b) :
    ∃ instructions : List (Option Bool), InstructionTrace m instructions a b ∧
      instructions.filterMap id = tokens.filterMap id := by
  induction tokens generalizing a with
  | nil => exact ⟨[],h,rfl⟩
  | cons token tokens ih =>
      obtain ⟨mid,hs,hr⟩ := h
      obtain ⟨first,hfirst,hlog⟩ := finite_macro_instructions m token a mid hs
      obtain ⟨rest,hrest,hlogs⟩ := ih mid hr
      refine ⟨first++rest,instruction_append m _ _ a mid b hfirst hrest,?_⟩
      rw [List.filterMap_append,hlog,hlogs]
      cases token <;> rfl

/-- Exact primitive charge inside a TM1 row, including loads, tests, writes,
movement and its final goto/halt. This is execution on the actual current tape,
not a host operation installed in the programme. -/
def rowOperations {L : Type} : TM1.Stmt (Alphabet m) L m.core.σ → m.core.σ → Tape (Alphabet m) → ℕ
  | .move d q,v,T => 1+rowOperations q v (T.move d)
  | .write f q,v,T => 1+rowOperations q v (T.write (f T.1 v))
  | .load f q,v,T => 1+rowOperations q (f T.1 v) T
  | .branch f q r,v,T => 1+if f T.1 v then rowOperations q v T else rowOperations r v T
  | .goto _,_,_ => 1
  | .halt,_,_ => 1

def rowSize {L : Type} : TM1.Stmt (Alphabet m) L m.core.σ → ℕ
  | .move _ q => 1+rowSize q
  | .write _ q => 1+rowSize q
  | .load _ q => 1+rowSize q
  | .branch _ q r => 1+max (rowSize q) (rowSize r)
  | .goto _ => 1
  | .halt => 1

theorem row_operations_le {L : Type} (q : TM1.Stmt (Alphabet m) L m.core.σ)
    (v : m.core.σ) (T : Tape (Alphabet m)) : rowOperations m q v T ≤ rowSize m q := by
  induction q generalizing v T with
  | move d q ih => exact Nat.add_le_add_left (ih v (T.move d)) 1
  | write f q ih => exact Nat.add_le_add_left (ih v (T.write (f T.1 v))) 1
  | load f q ih => exact Nat.add_le_add_left (ih (f T.1 v) T) 1
  | branch f q r ihq ihr =>
      cases h : f T.1 v
      · simpa [rowOperations,rowSize,h] using
          Nat.add_le_add_left ((ihr v T).trans (Nat.le_max_right (rowSize m q) _)) 1
      · simpa [rowOperations,rowSize,h] using
          Nat.add_le_add_left ((ihq v T).trans (Nat.le_max_left _ (rowSize m r))) 1
  | goto f => exact le_rfl
  | halt => exact le_rfl

def rowBudget : ℕ := ∑ l : Label m, (rowSize m ((programme m).core l)+rowSize m ((programme m).alternate l))

theorem row_budget (bit : Bool) (l : Label m) (v : m.core.σ) (T : Tape (Alphabet m)) :
    rowOperations m (if bit then (programme m).alternate l else (programme m).core l) v T ≤ rowBudget m := by
  classical
  have hl : rowSize m ((programme m).core l)+rowSize m ((programme m).alternate l) ≤ rowBudget m :=
    by
      unfold rowBudget
      exact Finset.single_le_sum (f := fun key => rowSize m ((programme m).core key) + rowSize m ((programme m).alternate key)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  cases bit
  · exact (row_operations_le m _ v T).trans ((Nat.le_add_right _ _).trans hl)
  · exact (row_operations_le m _ v T).trans ((Nat.le_add_left _ _).trans hl)

def transitionOperations (token : Option Bool) (c : FiniteCfg m) : ℕ :=
  match c.l,token with
  | none,_ => 0
  | some l,none => if (programme m).choose l then 0
      else rowOperations m ((programme m).core l) c.var c.Tape
  | some l,some b => if (programme m).choose l then
      rowOperations m (if b then (programme m).alternate l else (programme m).core l) c.var c.Tape
      else 0

theorem transition_operations_le (token : Option Bool) (c : FiniteCfg m) :
    transitionOperations m token c ≤ rowBudget m := by
  cases hl : c.l with
  | none => simp [transitionOperations,hl]
  | some l =>
      cases token with
      | none =>
          cases hs : (programme m).choose l
          · simpa [transitionOperations,hl,hs] using row_budget m false l c.var c.Tape
          · simp [transitionOperations,hl,hs]
      | some bit =>
          cases hs : (programme m).choose l
          · simp [transitionOperations,hl,hs]
          · simpa [transitionOperations,hl,hs] using row_budget m bit l c.var c.Tape

def instructionOperations : List (Option Bool) → FiniteCfg m → ℕ
  | [],_ => 0
  | token::tokens,c => transitionOperations m token c+
      ((finiteStep m token c).map (instructionOperations tokens)).getD 0

theorem instruction_operations_le (tokens : List (Option Bool)) (a b : FiniteCfg m)
    (h : InstructionTrace m tokens a b) :
    instructionOperations m tokens a ≤ tokens.length*rowBudget m := by
  induction tokens generalizing a with
  | nil => simp [instructionOperations]
  | cons token tokens ih =>
      obtain ⟨mid,hs,hr⟩ := h
      change transitionOperations m token a+
        ((finiteStep m token a).map (instructionOperations m tokens)).getD 0 ≤ _
      rw [hs,Option.map_some,Option.getD_some]
      calc
        transitionOperations m token a+instructionOperations m tokens mid ≤
            rowBudget m+tokens.length*rowBudget m :=
          Nat.add_le_add (transition_operations_le m token a) (ih mid hr)
        _ = (token::tokens).length*rowBudget m := by
          simp [Nat.add_mul,Nat.add_comm]

def input (word : List (m.core.Γ m.core.k₀)) : List (Alphabet m) := TM2to1.trInit m.core.k₀ word
def initial (word : List (m.core.Γ m.core.k₀)) : Cfg m := TM1.init (input m word)

theorem input_length (word : List (m.core.Γ m.core.k₀)) :
    (input m word).length = max 1 word.length := by
  simp only [input,TM2to1.trInit,List.length_cons,List.length_tail,List.length_map,List.length_reverse]
  omega

/-- Real compiler input encoding, with original main/initial state supplied
as defaults. It is NOT an arbitrary encoded configuration supplied as input. -/
theorem initial_encoded (word : List (m.core.Γ m.core.k₀)) :
    Encoded m (initList m.core word) (initial m word) := by
  have hi : (TM2.init m.core.k₀ word : m.Config) = initList m.core word := by
    unfold TM2.init initList
    congr 1
    funext k
    by_cases hk : k = m.core.k₀
    · subst k; simp
    · simp [Function.update_of_ne hk,hk]
  exact hi ▸ TM2to1.trCfg_init m.core.k₀ word

def finiteInitial (word : List (m.core.Γ m.core.k₀)) : FiniteCfg m :=
  ⟨some (programme m).main,(programme m).initialState,(initial m word).Tape⟩

theorem finite_initial_forget (word : List (m.core.Γ m.core.k₀)) :
    forget m (finiteInitial m word) = initial m word := rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TapeSimulation
