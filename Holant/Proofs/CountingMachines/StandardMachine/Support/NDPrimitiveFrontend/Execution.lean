import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveDispatcher.Source
import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveFrontend.Program

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Literal, clocked tape scan producers of the actual
frontend table. Lists here describe observed finite tape frames in proofs;
the running programme only performs head reads, moves and symbol writes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveFrontend.Execution
open Turing Computability Holant.Complexity
open Program
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
@[simp] theorem symbol_default : (default : Symbol w) = Symbol.native default := rfl
@[simp] theorem mk_nativeblank : (ListBlank.mk [Symbol.native default] : ListBlank (Symbol w)) = ListBlank.mk [] :=
  Quotient.sound' (Or.inr ⟨1,rfl⟩)
@[simp] theorem trim_nativeblanks (xs : List (Symbol w)) (n : ℕ) :
    ListBlank.mk (xs ++ List.replicate n (Symbol.native default)) = ListBlank.mk xs :=
  Quotient.sound' (Or.inr ⟨n,rfl⟩)
@[simp] theorem native_default : (default : Native.Control (machine w)) =
    (.inl (TapeSimulation.programme (machine w)).main,(TapeSimulation.programme (machine w)).initialState) := rfl
def cfg (state : Front) (L R : List (Symbol w)) : Cfg w := ⟨.inl state,Tape.mk₂ L R⟩
def Rows : ℕ → Cfg w → Cfg w → Prop
  | 0,a,b => a = b
  | n+1,a,b => ∃ next, step w none a = some next ∧ Rows n next b
theorem append (n k : ℕ) (a mid b : Cfg w) (hn : Rows w n a mid) (hk : Rows w k mid b) : Rows w (n+k) a b := by
  induction n generalizing a with
  | zero => subst a; simpa only [Nat.zero_add] using hk
  | succ n ih =>
      rw [Nat.succ_add]
      obtain ⟨next,hs,hr⟩ := hn
      exact ⟨next,hs,ih next hr⟩

theorem right_step (s t : Front) (L R : List (Symbol w)) (a : Symbol w)
    (h : frontTable w s a = some (.inl t,.move .right)) :
    step w none (cfg w s L (a::R)) = some (cfg w t (a::L) R) := by
  simp [step,choose,table,cfg,TM0.step,Tape.mk₂,Tape.mk',h,ListBlank.head_mk,ListBlank.tail_mk,
    Tape.move,Tape.move_right_mk',ListBlank.cons_mk]
theorem left_step (s t : Front) (L R : List (Symbol w)) (a : Symbol w)
    (h : frontTable w s a = some (.inl t,.move .left)) :
    step w none (cfg w s L (a::R)) = some (cfg w t L.tail (L.headI::a::R)) := by
  simp [step,choose,table,cfg,TM0.step,Tape.mk₂,Tape.mk',h,ListBlank.head_mk,ListBlank.tail_mk,
    Tape.move,Tape.move_left_mk',ListBlank.cons_mk]
theorem write_step (s t : Front) (L R : List (Symbol w)) (a b : Symbol w)
    (h : frontTable w s a = some (.inl t,.write b)) :
    step w none (cfg w s L (a::R)) = some (cfg w t L (b::R)) := by
  simp [step,choose,table,cfg,TM0.step,Tape.mk₂,Tape.mk',h,ListBlank.head_mk,ListBlank.tail_mk,Tape.write_mk]

theorem right_scan (s : Front) (xs L R : List (Symbol w))
    (h : ∀ a ∈ xs, frontTable w s a = some (.inl s,.move .right)) :
    Rows w xs.length (cfg w s L (xs++R)) (cfg w s (xs.reverse++L) R) := by
  induction xs generalizing L with
  | nil => rfl
  | cons a xs ih =>
      have ha := h a (by simp)
      have hr := ih (a::L) (fun b hb => h b (by simp [hb]))
      refine ⟨cfg w s (a::L) (xs++R),right_step w s s L (xs++R) a ha,?_⟩
      simpa [List.reverse_cons,List.append_assoc] using hr

/-- Scan the entire current/left segment, stopping on the first physical
blank beyond it. The zero-length case performs no phantom scan step. -/
theorem left_scan (s : Front) (xs R : List (Symbol w))
    (h : ∀ a ∈ xs, frontTable w s a = some (.inl s,.move .left)) :
    Rows w xs.length (cfg w s xs.tail (xs.headI::R))
      (cfg w s [] (default::xs.reverse++R)) := by
  induction xs generalizing R with
  | nil => rfl
  | cons a xs ih =>
      have ha := h a (by simp)
      have hr := ih (a::R) (fun b hb => h b (by simp [hb]))
      refine ⟨cfg w s xs.tail (xs.headI::a::R),left_step w s s xs R a ha,?_⟩
      simpa [List.reverse_cons,List.append_assoc] using hr

/-- returnLeft/copyLeft/finishLeft traverse actual cells to the installed
fence. They do not infer a length or erase a supplied header for free. -/
theorem to_fence (s : Front) (xs L R : List (Symbol w))
    (h : ∀ a : Symbol w, a ≠ .fence → frontTable w s a = some (.inl s,.move .left))
    (hxs : ∀ a ∈ xs, a ≠ .fence) (hR : R.headI ≠ .fence) :
    Rows w (xs.length+1) (cfg w s (xs++.fence::L) R)
      (cfg w s L (.fence::xs.reverse++R)) := by
  induction xs generalizing R with
  | nil =>
      refine ⟨cfg w s L (.fence::R),?_,rfl⟩
      cases R with
      | nil =>
          have hblank := h (Symbol.native default) (by simp)
          simp [step,choose,table,cfg,TM0.step,Tape.mk₂,Tape.mk',hblank,ListBlank.head_mk,ListBlank.tail_mk,
            Tape.move,Tape.move_left_mk',ListBlank.cons_mk]
      | cons a R => simpa using left_step w s s (.fence::L) R a (h a hR)
  | cons a xs ih =>
      have ha := hxs a (by simp)
      have hr := ih (a::R) (fun b hb => hxs b (by simp [hb])) ha
      refine ⟨cfg w s (xs++.fence::L) (a::R),?_,?_⟩
      · cases R with
        | nil =>
            have hblank := h (Symbol.native default) (by simp)
            simp [step,choose,table,cfg,TM0.step,Tape.mk₂,Tape.mk',hblank,ListBlank.head_mk,ListBlank.tail_mk,
              Tape.move,Tape.move_left_mk',ListBlank.cons_mk]
        | cons r R => simpa using left_step w s s (a::(xs++.fence::L)) R r (h r hR)
      · simpa [List.reverse_cons,List.append_assoc] using hr

def frame (pre rest : List Bool) : Cfg w := cfg w .backFence
  (pre.map (fun b => .native (column w b)))
  (.fence::List.replicate pre.length default++rawWord w rest++[.eof])

/-- The first pass only scans original raw letters. It installs the EOF and
returns to the genuinely written fence in exactly 2*N+6 physical rows. -/
theorem install_markers (word : List Bool) : Rows w (2*word.length+6) (initial w word) (frame w [] word) := by
  let input := rawWord w word
  have hstart : Rows w 3 (initial w word) (cfg w .scanEnd [.fence] input) := by
    refine ⟨⟨.inl .putFence,(initial w word).Tape.move .left⟩,rfl,
      ⟨.inl .toInput,((initial w word).Tape.move .left).write .fence⟩,rfl,
      cfg w .scanEnd [.fence] input,?_,rfl⟩
    simp [initial,rawWord,input,cfg,step,choose,table,frontTable,TM0.step,TM0.init,Tape.mk₁,Tape.mk₂,Tape.mk',
      Tape.move,Tape.move_left_mk',Tape.move,Tape.move_right_mk',ListBlank.head_mk,ListBlank.tail_mk,ListBlank.cons_mk]
  have hscan := right_scan w .scanEnd input [.fence] [] (by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    rfl)
  simp only [List.append_nil] at hscan
  have hwrite : Rows w 1 (cfg w .scanEnd (input.reverse++[.fence]) [])
      (cfg w .returnLeft (input.reverse++[.fence]) [.eof]) := by
    refine ⟨_,?_,rfl⟩
    simp [cfg,step,choose,table,frontTable,TM0.step,Tape.mk₂,Tape.mk',ListBlank.head_mk,ListBlank.tail_mk]
  have hreturn := to_fence w .returnLeft input.reverse [] [.eof]
    (by intro a ha; cases a <;> simp_all [frontTable])
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha); simp)
    (by simp)
  have hstop : Rows w 1 (cfg w .returnLeft [] (.fence::input++[.eof])) (frame w [] word) := by
    refine ⟨_,?_,rfl⟩
    exact write_step w .returnLeft .backFence [] (input++[.eof]) .fence .fence rfl
  have hall := append w 3 input.length _ _ _ hstart hscan
  have hall := append w (3+input.length) 1 _ _ _ hall hwrite
  have hall := append w (3+input.length+1) (input.length+1) _ _ _ hall (by simpa using hreturn)
  have hall := append w (3+input.length+1+(input.length+1)) 1 _ _ _ hall hstop
  simpa [input,rawWord,List.length_map,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,Nat.mul_succ,Nat.mul_zero] using hall

theorem snoc_blanks (n : ℕ) : (List.replicate n (default : Symbol w))++[default] = List.replicate (n+1) default := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (default :: ·) ih

/-- One real input byte is erased, carried in finite Bool control, written
once to the left output stack, and the head returns to the same fence. -/
theorem copy_round (pre rest : List Bool) (b : Bool) :
    Rows w (4*pre.length+6) (frame w pre (b::rest)) (frame w (pre++[b]) rest) := by
  let cols : List (Symbol w) := pre.map (fun a => .native (column w a))
  let blanks : List (Symbol w) := List.replicate pre.length default
  let suffix := rawWord w rest++[.eof]
  have first : Rows w 1 (frame w pre (b::rest))
      (cfg w .skipInput (.fence::cols) (blanks++.raw b::suffix)) :=
    ⟨_,right_step w .backFence .skipInput cols _ .fence rfl,by
      simp [Rows,rawWord,blanks,suffix,List.append_assoc]⟩
  have skip := right_scan w .skipInput blanks (.fence::cols) (.raw b::suffix) (by
    intro a ha
    have he : a = default := (List.mem_replicate.mp ha).2
    subst a
    simp [frontTable])
  have erase : Rows w 1 (cfg w .skipInput (blanks.reverse++.fence::cols) (.raw b::suffix))
      (cfg w (.copyLeft b) (blanks.reverse++.fence::cols) (default::suffix)) :=
    ⟨_,write_step w .skipInput (.copyLeft b) _ suffix (.raw b) default rfl,rfl⟩
  have back := to_fence w (.copyLeft b) blanks.reverse cols (default::suffix)
    (by intro a ha; cases a <;> simp_all [frontTable])
    (by intro a ha; have he : a = default := (List.mem_replicate.mp (List.mem_reverse.mp ha)).2; subst a; simp)
    (by simp)
  have enter : Rows w 1 (cfg w (.copyLeft b) cols (.fence::blanks++default::suffix))
      (cfg w (.outLeft b) cols.tail (cols.headI::.fence::blanks++default::suffix)) :=
    ⟨_,left_step w (.copyLeft b) (.outLeft b) cols _ .fence rfl,rfl⟩
  have out := left_scan w (.outLeft b) cols (.fence::blanks++default::suffix) (by
    intro a ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    simp [frontTable,column_ne_blank])
  have put : Rows w 1 (cfg w (.outLeft b) [] (default::cols.reverse++.fence::blanks++default::suffix))
      (cfg w .backFence [] (.native (column w b)::cols.reverse++.fence::blanks++default::suffix)) :=
    ⟨_,write_step w (.outLeft b) .backFence [] _ default (.native (column w b)) (by simp [frontTable]),rfl⟩
  simp only [List.append_assoc] at put
  have home := right_scan w .backFence (.native (column w b)::cols.reverse) [] (.fence::blanks++default::suffix)
    (by intro a ha; rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha); rfl)
  have hall := append w 1 blanks.length _ _ _ first skip
  have hall := append w (1+blanks.length) 1 _ _ _ hall erase
  have hall := append w (1+blanks.length+1) (blanks.length+1) _ _ _ hall (by simpa using back)
  have hall := append w (1+blanks.length+1+(blanks.length+1)) 1 _ _ _ hall enter
  have hall := append w (1+blanks.length+1+(blanks.length+1)+1) cols.length _ _ _ hall out
  have hall := append w (1+blanks.length+1+(blanks.length+1)+1+cols.length) 1 _ _ _ hall put
  have hall := append w (1+blanks.length+1+(blanks.length+1)+1+cols.length+1) (cols.length+1) _ _ _ hall (by simpa only [List.length_cons,List.length_reverse,List.append_nil] using home)
  simpa [frame,cfg,cols,blanks,suffix,rawWord,List.map_append,List.reverse_cons,List.reverse_reverse,
    List.append_assoc,List.length_map,List.length_replicate,List.length_append,snoc_blanks,List.replicate_add,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,Nat.mul_succ,Nat.mul_zero] using hall

def copySteps (i n : ℕ) : ℕ := 2*n*n+4*i*n+4*n
theorem copy_steps_succ (i n : ℕ) : copySteps i (n+1) = (4*i+6)+copySteps (i+1) n := by
  unfold copySteps
  ring
theorem copy_all (pre rest : List Bool) :
    Rows w (copySteps pre.length rest.length) (frame w pre rest) (frame w (pre++rest) []) := by
  induction rest generalizing pre with
  | nil => simp [copySteps,Rows]
  | cons b rest ih =>
      have hr := copy_round w pre rest b
      have ht := ih (pre++[b])
      rw [List.length_cons,copy_steps_succ]
      exact append w _ _ _ _ _ hr (by simpa [List.length_append,List.append_assoc] using ht)

theorem trim_blanks (xs : List (Symbol w)) (n : ℕ) :
    ListBlank.mk (xs++List.replicate n default) = ListBlank.mk xs :=
  Quotient.sound' (Or.inr ⟨n,rfl⟩)

/-- The final pass physically erases EOF/fence and moves to the farthest
copied bit before writing its bottom flag. Empty input still writes the
single genuine bottom row. This is an equality of complete actual tapes. -/
theorem finish_before (word : List Bool) :
    ∃ before : Cfg w, before.q.isLeft = true ∧ Rows w (3*word.length+6) (frame w word []) before ∧
      step w none before = some (lift w (NDPrimitiveDispatcher.Paths.initial w word)) := by
  let cols : List (Symbol w) := word.map (fun b => .native (column w b))
  let blanks : List (Symbol w) := List.replicate word.length default
  have first : Rows w 1 (frame w word []) (cfg w .skipInput (.fence::cols) (blanks++[.eof])) :=
    ⟨_,right_step w .backFence .skipInput cols _ .fence rfl,by
      simp [Rows,rawWord,blanks,List.append_assoc]⟩
  have skip := right_scan w .skipInput blanks (.fence::cols) [.eof] (by
    intro a ha
    have he : a = default := (List.mem_replicate.mp ha).2
    subst a
    simp [frontTable])
  have eraseEnd : Rows w 1 (cfg w .skipInput (blanks.reverse++.fence::cols) [.eof])
      (cfg w .finishLeft (blanks.reverse++.fence::cols) [default]) :=
    ⟨_,write_step w .skipInput .finishLeft _ [] .eof default rfl,rfl⟩
  have home := to_fence w .finishLeft blanks.reverse cols [default]
    (by intro a ha; cases a <;> simp_all [frontTable])
    (by intro a ha; have he : a = default := (List.mem_replicate.mp (List.mem_reverse.mp ha)).2; subst a; simp)
    (by simp)
  have eraseFence : Rows w 1 (cfg w .finishLeft cols (.fence::blanks++[default]))
      (cfg w .leftStart cols (default::blanks++[default])) :=
    ⟨_,write_step w .finishLeft .leftStart cols _ .fence default rfl,rfl⟩
  have left : Rows w 1 (cfg w .leftStart cols (default::blanks++[default]))
      (cfg w .seekBottom cols.tail (cols.headI::default::blanks++[default])) :=
    ⟨_,left_step w .leftStart .seekBottom cols _ default rfl,rfl⟩
  have scan := left_scan w .seekBottom cols (default::blanks++[default]) (by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    simp [frontTable,column_ne_blank])
  have right : Rows w 1 (cfg w .seekBottom [] (default::cols.reverse++default::blanks++[default]))
      (cfg w .markBottom [default] (cols.reverse++default::blanks++[default])) :=
    ⟨_,right_step w .seekBottom .markBottom [] _ default (by simp [frontTable]),rfl⟩
  simp only [List.append_assoc] at right
  have mark : Rows w 1 (cfg w .markBottom [default] (cols.reverse++default::blanks++[default]))
      (lift w (NDPrimitiveDispatcher.Paths.initial w word)) := by
    refine ⟨_,?_,rfl⟩
    have hcols : cols.reverse = word.reverse.map (fun b => Symbol.native (column w b)) := by
      simp [cols,List.map_reverse]
    have hleft : (ListBlank.mk [default] : ListBlank (Symbol w)) = ListBlank.mk [] := by
      simpa using trim_blanks w [] 1
    have htail : default::blanks++[default] = List.replicate (word.length+2) (default : Symbol w) := by
      exact congrArg (fun xs : List (Symbol w) => default :: xs) (snoc_blanks w word.length)
    simp only [symbol_default] at hleft htail
    cases hrev : word.reverse with
    | nil =>
        have hw : word = [] := List.reverse_eq_nil_iff.mp hrev
        subst word
        simp [cfg,cols,blanks,lift,NDPrimitiveDispatcher.Paths.initial,NDPrimitiveDispatcher.Program.embed,
          NDPrimitiveDispatcher.Program.haltCfg,PathSegmentation.start,TapeSimulation.finiteInitial,
          TapeSimulation.initial,TapeSimulation.input,TM2to1.trInit,step,choose,table,frontTable,
          TM0.step,TM1.init,Tape.mk₁,Tape.mk₂,Tape.mk',Tape.map,ListBlank.map_mk,
          ListBlank.head_mk,ListBlank.tail_mk,hleft,trim_blanks,bottom,inclusion,TM0.init]
    | cons b bs =>
        simp [cfg,hcols,hrev,htail,lift,NDPrimitiveDispatcher.Paths.initial,NDPrimitiveDispatcher.Program.embed,
          PathSegmentation.start,TapeSimulation.finiteInitial,TapeSimulation.initial,TapeSimulation.input,
          TM2to1.trInit,column,bottom,step,choose,table,frontTable,TM0.step,TM1.init,
          Tape.mk₁,Tape.mk₂,Tape.mk',Tape.map,ListBlank.map_mk,ListBlank.head_mk,ListBlank.tail_mk,
          hleft,trim_blanks,List.map_map,inclusion,TM0.init,Function.comp_def] <;> rfl
  have hall := append w 1 blanks.length _ _ _ first skip
  have hall := append w (1+blanks.length) 1 _ _ _ hall eraseEnd
  have hall := append w (1+blanks.length+1) (blanks.length+1) _ _ _ hall (by simpa using home)
  have hall := append w (1+blanks.length+1+(blanks.length+1)) 1 _ _ _ hall eraseFence
  have hall := append w (1+blanks.length+1+(blanks.length+1)+1) 1 _ _ _ hall left
  have hall := append w (1+blanks.length+1+(blanks.length+1)+1+1) cols.length _ _ _ hall scan
  have hall := append w (1+blanks.length+1+(blanks.length+1)+1+1+cols.length) 1 _ _ _ hall right
  obtain ⟨target,hmark,hend⟩ := mark
  refine ⟨cfg w .markBottom [default] (cols.reverse++default::blanks++[default]),rfl,?_,?_⟩
  · simpa [cols,blanks,List.length_map,List.length_replicate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,Nat.mul_succ,Nat.mul_zero] using hall
  · exact hend ▸ hmark

theorem finish (word : List Bool) : Rows w (3*word.length+7) (frame w word [])
    (lift w (NDPrimitiveDispatcher.Paths.initial w word)) := by
  obtain ⟨before,hfront,hr,hs⟩ := finish_before w word
  exact append w (3*word.length+6) 1 _ _ _ hr ⟨_,hs,rfl⟩

def steps (N : ℕ) : ℕ := 2*N*N+9*N+13
def polynomial : Polynomial ℕ := 2*Polynomial.X*Polynomial.X+9*Polynomial.X+13
theorem polynomial_eval (N : ℕ) : polynomial.eval N = steps N := by simp [polynomial,steps]
theorem prepare (word : List Bool) : Rows w (steps word.length) (initial w word)
    (lift w (NDPrimitiveDispatcher.Paths.initial w word)) := by
  have first := install_markers w word
  have copy := copy_all w [] word
  have last := finish w word
  have hcopy : Rows w (copySteps 0 word.length) (frame w [] word) (frame w word []) := by simpa using copy
  have hall := append w (2*word.length+6) (copySteps 0 word.length) _ _ _ first hcopy
  have hall := append w (2*word.length+6+copySteps 0 word.length) (3*word.length+7) _ _ _ hall last
  convert hall using 1
  unfold steps copySteps
  ring

/-- All but the last preparation row endpoint in genuine finite frontend control.
This producer prevents the physical nondeterministic suffix from being
silently used while proving the deterministic initialization. -/
theorem prepare_before (word : List Bool) :
    ∃ before : Cfg w, before.q.isLeft = true ∧
      Rows w (steps word.length-1) (initial w word) before ∧
      step w none before = some (lift w (NDPrimitiveDispatcher.Paths.initial w word)) := by
  obtain ⟨before,hfront,hfinish,hstep⟩ := finish_before w word
  have first := install_markers w word
  have copy : Rows w (copySteps 0 word.length) (frame w [] word) (frame w word []) := by simpa using copy_all w [] word
  have hall := append w (2*word.length+6) (copySteps 0 word.length) _ _ _ first copy
  have hall := append w (2*word.length+6+copySteps 0 word.length) (3*word.length+6) _ _ _ hall hfinish
  refine ⟨before,hfront,?_,hstep⟩
  convert hall using 1
  have he : steps word.length = (2*word.length+6+copySteps 0 word.length+(3*word.length+6))+1 := by
    unfold steps copySteps
    ring
  rw [he]
  omega

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveFrontend.Execution
