import Holant.Proofs.CountingMachines.StandardMachine.Support.TapeMicrostepBudgetCore
import Holant.Proofs.CountingMachines.StandardMachine.Support.PathSegmentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TapeMicrostepBudget
open Turing Computability Holant.Complexity StateTransition Relation
local instance (m : BinaryMachine) : Fintype m.core.Λ := m.core.ΛFin
local instance (m : BinaryMachine) : Fintype m.core.σ := m.core.σFin
section Witness
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)
abbrev machine := TotalRawSource.source w

/-- Sole source entry; the table and branch sites are unchanged. -/
def source := TapeSimulation.source w

/-- Capacity for every actual source pre, even a longer held-halt suffix.
The deadline and shorter endpoint are derived, not supplied as input. -/
theorem source_capacity (word : List Bool) (tokens : List (Option Bool)) (c : (machine w).Config)
    (htrace : (machine w).TraceValid tokens (initList (machine w).core word) c) :
    ∀ k, (c.stk k).length ≤ (TotalRawSource.capacityPolynomial w).eval word.length := by
  by_cases hlen : tokens.length ≤ TotalRawSource.horizon w word
  · exact (TotalRawSource.all_path_resources w word tokens c hlen htrace).1
  · have hge : TotalRawSource.horizon w word ≤ tokens.length := by omega
    obtain ⟨mid,hpre,hpost⟩ := (BooleanOpcode.NativeExecution.trace_append (machine w)
      (tokens.take (TotalRawSource.horizon w word)) (tokens.drop (TotalRawSource.horizon w word)) _ _).mp
        (by simpa only [List.take_append_drop] using htrace)
    have htake : (tokens.take (TotalRawSource.horizon w word)).length = TotalRawSource.horizon w word := by
      simp [List.length_take,Nat.min_eq_left hge]
    have hh := (TotalRawSource.all_paths_halt w word _ mid htake hpre).1
    have he := ((BooleanOpcode.NativeExecution.trace_halt_iff (machine w) _ mid c hh).mp hpost).1
    exact he ▸ (TotalRawSource.all_path_resources w word _ mid (by omega) hpre).1

def microPolynomial : Polynomial ℕ :=
  TotalRawSource.timePolynomial w *
    (Polynomial.C 1+Polynomial.C (actionBudget (machine w))*
      (Polynomial.C 2*(TotalRawSource.capacityPolynomial w+Polynomial.C (actionBudget (machine w)))+Polynomial.C 3))

theorem micro_polynomial_eval (word : List Bool) :
    (microPolynomial w).eval word.length = TotalRawSource.horizon w word*
      rowBound (machine w) ((TotalRawSource.capacityPolynomial w).eval word.length) := by
  simp [microPolynomial,TotalRawSource.horizon,rowBound]

/-- Each actual source row receives its own concrete transcript. The current
source pre produces capacity at every recursive call; no row/path clock
or supplied decomposition budget is a hypothesis. -/
theorem path_instructions (word : List Bool) (before tokens : List (Option Bool))
    (c d : (machine w).Config) (a : FiniteCfg (machine w))
    (hbefore : (machine w).TraceValid before (initList (machine w).core word) c)
    (htrace : (machine w).TraceValid tokens c d)
    (he : TapeSimulation.Encoded (machine w) c (TapeSimulation.forget (machine w) a)) :
    ∃ b : FiniteCfg (machine w), ∃ instructions : List (Option Bool),
      TapeSimulation.Encoded (machine w) d (TapeSimulation.forget (machine w) b) ∧
      TapeSimulation.InstructionTrace (machine w) instructions a b ∧
      instructions.filterMap id = tokens.filterMap id ∧
      instructions.length ≤ tokens.length*rowBound (machine w) ((TotalRawSource.capacityPolynomial w).eval word.length) := by
  induction tokens generalizing before c a with
  | nil =>
      change c = d at htrace
      subst d
      exact ⟨a,[],he,rfl,rfl,by simp⟩
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := htrace
      have hB := source_capacity w word before c hbefore
      obtain ⟨mid,first,hmid,hfirst,hlog,hfee⟩ := source_edge (machine w) token c next a hs he _ hB
      have hpre : (machine w).TraceValid (before++[token]) (initList (machine w).core word) next := by
        apply (BooleanOpcode.NativeExecution.trace_append (machine w) before [token] _ _).mpr
        exact ⟨c,hbefore,next,hs,rfl⟩
      obtain ⟨b,rest,hb,hrest,hlogs,hbound⟩ := ih (before++[token]) next mid hpre hr hmid
      refine ⟨b,first++rest,hb,TapeSimulation.instruction_append (machine w) _ _ a mid b hfirst hrest,?_,?_⟩
      · rw [List.filterMap_append,hlog,hlogs]
        cases token <;> rfl
      · calc
          (first++rest).length = first.length+rest.length := List.length_append
          _ ≤ rowBound (machine w) ((TotalRawSource.capacityPolynomial w).eval word.length)+
                tokens.length*rowBound (machine w) ((TotalRawSource.capacityPolynomial w).eval word.length) :=
            Nat.add_le_add hfee hbound
          _ = (token::tokens).length*rowBound (machine w) ((TotalRawSource.capacityPolynomial w).eval word.length) := by
            simp [Nat.add_mul,Nat.add_comm]

/-- Every legal source pre, including arbitrarily many canonical held
rows, has an actual finite tape transcript within the SAME uniform clock. -/
theorem source_path_time (word : List Bool) (tokens : List (Option Bool)) (d : (machine w).Config)
    (htrace : (machine w).TraceValid tokens (initList (machine w).core word) d) :
    ∃ b : FiniteCfg (machine w), ∃ instructions : List (Option Bool),
      TapeSimulation.Encoded (machine w) d (TapeSimulation.forget (machine w) b) ∧
      TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) b ∧
      instructions.filterMap id = tokens.filterMap id ∧ instructions.length ≤ (microPolynomial w).eval word.length := by
  by_cases hlen : tokens.length ≤ TotalRawSource.horizon w word
  · obtain ⟨b,micro,hb,hr,hlog,hbound⟩ := path_instructions w word [] tokens _ d (PathSegmentation.start w word) rfl htrace
      (TapeSimulation.initial_encoded (machine w) word)
    refine ⟨b,micro,hb,hr,hlog,?_⟩
    rw [micro_polynomial_eval]
    exact hbound.trans (Nat.mul_le_mul_right _ hlen)
  · have hge : TotalRawSource.horizon w word ≤ tokens.length := by omega
    obtain ⟨mid,hpre,hpost⟩ := (BooleanOpcode.NativeExecution.trace_append (machine w)
      (tokens.take (TotalRawSource.horizon w word)) (tokens.drop (TotalRawSource.horizon w word)) _ _).mp
        (by simpa only [List.take_append_drop] using htrace)
    have htake : (tokens.take (TotalRawSource.horizon w word)).length = TotalRawSource.horizon w word := by
      simp [List.length_take,Nat.min_eq_left hge]
    have hh := (TotalRawSource.all_paths_halt w word _ mid htake hpre).1
    have hhold := (BooleanOpcode.NativeExecution.trace_halt_iff (machine w) _ mid d hh).mp hpost
    obtain ⟨b,micro,hb,hr,hlog,hbound⟩ := path_instructions w word [] _ _ mid (PathSegmentation.start w word) rfl hpre
      (TapeSimulation.initial_encoded (machine w) word)
    refine ⟨b,micro,hhold.1 ▸ hb,hr,?_,?_⟩
    · have hlogs : tokens.filterMap id = (tokens.take (TotalRawSource.horizon w word)).filterMap id := by
        conv_lhs => rw [← List.take_append_drop (TotalRawSource.horizon w word) tokens]
        rw [List.filterMap_append,hhold.2]
        simp
      exact hlog.trans hlogs.symm
    · rw [micro_polynomial_eval]
      simpa only [htake] using hbound

/-- ALL unfinished physical prefixes extend to real halt. Complete the
observed guess stream only in this proof, use the actual all-raw source run,
then compare actual rows. The programme never receives a branch-log tape. -/
theorem prefix_completion (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint) :
    ∃ rest final, TapeSimulation.InstructionTrace (machine w) rest endpoint final ∧ final.l = none ∧
      (instructions++rest).length ≤ (microPolynomial w).eval word.length := by
  let padding : List Bool := List.replicate (TotalRawSource.choiceLength w word) false
  let log : List Bool := instructions.filterMap id++padding
  let first := log.take (TotalRawSource.choiceLength w word)
  let unused := log.drop (TotalRawSource.choiceLength w word)
  have hge : TotalRawSource.choiceLength w word ≤ log.length := by
    simp only [log,padding,List.length_append,List.length_replicate]
    omega
  have hlen : first.length = TotalRawSource.choiceLength w word := by
    simp only [first,List.length_take,Nat.min_eq_left hge]
  have hsplit : first++unused = log := List.take_append_drop _ _
  have hrun : (machine w).run (TotalRawSource.horizon w word) (log,initList (machine w).core word) =
      some (unused,TotalRawSource.terminal w word first) := by
    simpa only [hsplit] using TotalRawSource.all_raw_run w word first unused hlen
  obtain ⟨tokens,htime,hguesses,hsource⟩ := (machine w).run_trace (TotalRawSource.horizon w word)
    (log,initList (machine w).core word) (unused,TotalRawSource.terminal w word first) hrun
  obtain ⟨final,micro,hcoded,hmicro,hlogs,hbound⟩ := source_path_time w word tokens _ hsource
  have hhalt : final.l = none := by
    have hl := TapeSimulation.encoded_label (machine w) _ _ hcoded
    have ht := TotalRawSource.terminal_halts w word first
    cases hf : final.l with
    | none => rfl
    | some label => simp [TapeSimulation.forget,ht,hf] at hl
  have hstream : instructions.filterMap id++padding = micro.filterMap id++unused := by
    rw [hlogs]
    exact hguesses.symm
  obtain ⟨rest,hcut,hrest⟩ := instruction_prefix (machine w) instructions micro _ endpoint final
    htrace hmicro hhalt padding unused hstream
  exact ⟨rest,final,hrest,hhalt,by simpa only [hcut] using hbound⟩

theorem prefix_time (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint) :
    instructions.length ≤ (microPolynomial w).eval word.length := by
  obtain ⟨rest,final,hr,hh,hbound⟩ := prefix_completion w word instructions endpoint htrace
  rw [List.length_append] at hbound
  omega

/-- At the internally derived deadline any actual trajectory has already
halted; this statement has no halt/accepted endpoint premise. -/
theorem prefix_deadline (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint)
    (hlen : instructions.length = (microPolynomial w).eval word.length) : endpoint.l = none := by
  obtain ⟨rest,final,hr,hh,hbound⟩ := prefix_completion w word instructions endpoint htrace
  have hz : rest.length = 0 := by rw [List.length_append,hlen] at hbound; omega
  have he : rest = [] := List.length_eq_zero_iff.mp hz
  subst rest
  change endpoint = final at hr
  exact hr.symm ▸ hh

/-- The complete source rows in an arbitrary unfinished path are reflected
from its internally obtained partial segmentation; capacity and horizon are
the original source producers, not parameters supplied by the path caller. -/
theorem source_prefix_segmentation (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint) :
    ∃ done pending tokens mid c, instructions = done++pending ∧
      TapeSimulation.InstructionTrace (machine w) done (PathSegmentation.start w word) mid ∧
      PathSegmentation.ActiveTrace (machine w) tokens (initList (machine w).core word) c ∧
      TapeSimulation.Encoded (machine w) c (TapeSimulation.forget (machine w) mid) ∧
      Pending (machine w) pending mid endpoint ∧ done.filterMap id = tokens.filterMap id ∧
      tokens.length ≤ TotalRawSource.horizon w word ∧
      ∀ k, (c.stk k).length ≤ (TotalRawSource.capacityPolynomial w).eval word.length := by
  obtain ⟨done,pending,tokens,mid,hcut,hdone,hreal,hpending,hlog⟩ :=
    prefix_segmentation (machine w) instructions _ endpoint (PathSegmentation.start_boundary w word) htrace
  obtain ⟨c,hsource,hcoded⟩ := PathSegmentation.real_reflects (machine w) tokens _ _ mid
    (TapeSimulation.initial_encoded (machine w) word) hreal
  exact ⟨done,pending,tokens,mid,c,hcut,hdone,hsource,hcoded,hpending,hlog,
    PathSegmentation.active_length w word tokens c hsource,
    source_capacity w word tokens c (PathSegmentation.active_old (machine w) tokens _ c hsource)⟩

/-- Uniform clock for arbitrary REAL unsegmented accepting instruction paths.
The path supplies no source segmentation: segment_spec constructs it, and
actual halting-transcript uniqueness identifies the measured original word. -/
theorem physical_time (word : List Bool) (p : PathSegmentation.PhysicalPath w word) :
    p.val.length ≤ (microPolynomial w).eval word.length := by
  obtain ⟨endpoint,hend,hreal,hlen,hlog,hseg⟩ := PathSegmentation.segment_spec w word p
  obtain ⟨d,hd,he⟩ := PathSegmentation.real_reflects (machine w) _ (initList (machine w).core word) (PathSegmentation.start w word) endpoint
    (TapeSimulation.initial_encoded (machine w) word) hreal
  obtain ⟨b,instructions,hb,htrace,hlogs,hbound⟩ := path_instructions w word [] _ _ d
    (PathSegmentation.start w word) rfl (PathSegmentation.active_old (machine w) _ _ d hd)
      (TapeSimulation.initial_encoded (machine w) word)
  have hdend : d = haltList (machine w).core [true] :=
    TapeSimulation.encoded_left_unique (machine w) d _ _ he hend
  have hb' := hdend ▸ hb
  let q : PathSegmentation.PhysicalPath w word := ⟨instructions,b,hb',htrace⟩
  have heq : q = p := PathSegmentation.physical_guess_injective w word q p (hlogs.trans hlog)
  have hwords : instructions = p.val := congrArg Subtype.val heq
  rw [hwords] at hbound
  rw [micro_polynomial_eval]
  exact hbound.trans (Nat.mul_le_mul_right _ hlen)

theorem halted_time (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint)
    (hhalt : endpoint.l = none) : instructions.length ≤ (microPolynomial w).eval word.length := by
  obtain ⟨tokens,hseg,hreal,hlog⟩ := PathSegmentation.segment_correct (machine w) instructions _ endpoint
    (PathSegmentation.start_boundary w word) (PathSegmentation.halt_boundary (machine w) endpoint hhalt) htrace
  obtain ⟨d,hd,he⟩ := PathSegmentation.real_reflects (machine w) tokens (initList (machine w).core word) (PathSegmentation.start w word) endpoint
    (TapeSimulation.initial_encoded (machine w) word) hreal
  have hlen := PathSegmentation.active_length w word tokens d hd
  obtain ⟨b,micro,hb,hr,hlogs,hbound⟩ := path_instructions w word [] tokens _ d
    (PathSegmentation.start w word) rfl (PathSegmentation.active_old (machine w) tokens _ d hd)
      (TapeSimulation.initial_encoded (machine w) word)
  have hlabel : d.l.map TM2to1.Λ'.normal = none := (TapeSimulation.encoded_label (machine w) d _ he).trans
    (by simp [TapeSimulation.forget,hhalt])
  have hd : d.l = none := by cases hl : d.l <;> simp_all
  have hbh : b.l = none := by
    have hl := TapeSimulation.encoded_label (machine w) d _ hb
    cases hlb : b.l with
    | none => rfl
    | some l => simp [TapeSimulation.forget,hd,hlb] at hl
  have hm := (PathSegmentation.instruction_unique (machine w) micro instructions _ b endpoint hr htrace
    hbh hhalt (hlogs.trans hlog)).1
  rw [hm] at hbound
  rw [micro_polynomial_eval]
  exact hbound.trans (Nat.mul_le_mul_right _ hlen)

theorem physical_primitive (word : List Bool) (p : PathSegmentation.PhysicalPath w word) :
    TapeSimulation.instructionOperations (machine w) p.val (PathSegmentation.start w word) ≤
      (microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) := by
  obtain ⟨b,hb,hr⟩ := p.property
  exact (TapeSimulation.instruction_operations_le (machine w) p.val _ b hr).trans
    (Nat.mul_le_mul_right _ (physical_time w word p))

theorem physical_shift (word : List Bool) (p : PathSegmentation.PhysicalPath w word) :
    -((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) ≤
      instructionShift (machine w) p.val (PathSegmentation.start w word) ∧
    instructionShift (machine w) p.val (PathSegmentation.start w word) ≤
      ((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) := by
  obtain ⟨b,hb,hr⟩ := p.property
  have hs := instruction_shift_bound (machine w) p.val _ b hr
  have hm : (p.val.length*TapeSimulation.rowBudget (machine w) : ℤ) ≤
      ((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_right (TapeSimulation.rowBudget (machine w)) (physical_time w word p)
  exact ⟨(neg_le_neg hm).trans hs.1,hs.2.trans hm⟩

theorem initial_space (word : List Bool) :
    Within (machine w) word.length (PathSegmentation.start w word).Tape := by
  have hs : ∀ k, ((initList (machine w).core word).stk k).length ≤ word.length := by
    intro k
    by_cases hk : k = (machine w).core.k₀
    · subst k; simp [initList]
    · simp [initList,hk]
  have he := TapeSimulation.initial_encoded (machine w) word
  have hl := TapeSimulation.encoded_left_blank (machine w) _ _ he
  have hr := TapeSimulation.encoded_cells (machine w) _ _ he word.length hs
  intro i hi
  cases i with
  | ofNat n =>
      change (n : ℤ) < -(word.length : ℤ) ∨ (word.length : ℤ) < (n : ℤ) at hi
      have hn := hr n (by omega)
      change (TapeSimulation.initial (machine w) word).Tape.nth (n : ℤ) = default
      simpa only [Tape.right₀_nth] using hn
  | negSucc n =>
      change (TapeSimulation.initial (machine w) word).Tape.left.nth n = default
      rw [hl]
      change (ListBlank.mk ([] : List (TapeSimulation.Alphabet (machine w)))).nth n = default
      rw [ListBlank.nth_mk,List.getI_nil]

def spacePolynomial : Polynomial ℕ := Polynomial.X+microPolynomial w*Polynomial.C (TapeSimulation.rowBudget (machine w))

theorem space_eval (word : List Bool) : (spacePolynomial w).eval word.length =
    word.length+(microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) := by
  simp [spacePolynomial]

/-- Every arbitrary actual microtrajectory pre, including a pre inside
an unfinished source statement, has this whole-tape support bound. -/
theorem prefix_space (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint) :
    Within (machine w) ((spacePolynomial w).eval word.length) endpoint.Tape := by
  have hs := instruction_space (machine w) instructions _ endpoint htrace word.length (initial_space w word)
  rw [space_eval]
  exact within_mono (machine w) _ _ _ hs
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (prefix_time w word instructions endpoint htrace)) word.length)

theorem prefix_primitive (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint) :
    TapeSimulation.instructionOperations (machine w) instructions (PathSegmentation.start w word) ≤
      (microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) :=
  (TapeSimulation.instruction_operations_le (machine w) instructions _ endpoint htrace).trans
    (Nat.mul_le_mul_right _ (prefix_time w word instructions endpoint htrace))

theorem prefix_shift (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint) :
    -((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) ≤
      instructionShift (machine w) instructions (PathSegmentation.start w word) ∧
    instructionShift (machine w) instructions (PathSegmentation.start w word) ≤
      ((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) := by
  have hs := instruction_shift_bound (machine w) instructions _ endpoint htrace
  have hm : (instructions.length*TapeSimulation.rowBudget (machine w) : ℤ) ≤
      ((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_right (TapeSimulation.rowBudget (machine w)) (prefix_time w word instructions endpoint htrace)
  exact ⟨(neg_le_neg hm).trans hs.1,hs.2.trans hm⟩

def innerSpacePolynomial : Polynomial ℕ := spacePolynomial w+Polynomial.C (TapeSimulation.rowBudget (machine w))
def visitedPolynomial : Polynomial ℕ := microPolynomial w*Polynomial.C (TapeSimulation.rowBudget (machine w))+
  Polynomial.C (TapeSimulation.rowBudget (machine w))
def absoluteSpacePolynomial : Polynomial ℕ := Polynomial.X+Polynomial.C 2*visitedPolynomial w
def storageBitsPolynomial : Polynomial ℕ := Polynomial.C (controlWidth (machine w))+
  Polynomial.C (symbolWidth (machine w))*(Polynomial.C 2*innerSpacePolynomial w+Polynomial.C 1)
def primitiveStorageBitsPolynomial : Polynomial ℕ := storageBitsPolynomial w+
  Polynomial.C (CellBits.width (PrimitiveControl (machine w)))

theorem inner_space_eval (word : List Bool) : (innerSpacePolynomial w).eval word.length =
    (spacePolynomial w).eval word.length+TapeSimulation.rowBudget (machine w) := by simp [innerSpacePolynomial]
theorem visited_eval (word : List Bool) : (visitedPolynomial w).eval word.length =
    (microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w)+TapeSimulation.rowBudget (machine w) := by
  simp [visitedPolynomial]
theorem absolute_space_eval (word : List Bool) : (absoluteSpacePolynomial w).eval word.length =
    word.length+2*((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w)+TapeSimulation.rowBudget (machine w)) := by
  simp [absoluteSpacePolynomial,visitedPolynomial]
theorem storage_bits_eval (word : List Bool) : (storageBitsPolynomial w).eval word.length =
    controlWidth (machine w)+symbolWidth (machine w)*(2*(innerSpacePolynomial w).eval word.length+1) := by
  simp [storageBitsPolynomial]

theorem prefix_inner_space (word : List Bool) (instructions : List (Option Bool))
    (mid : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) mid)
    (l : TapeSimulation.Label (machine w)) (bit : Bool)
    (n : ℕ) (u : (machine w).core.σ) (U : Tape (TapeSimulation.Alphabet (machine w)))
    (hp : RowPrefix (machine w)
      (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
      mid.var mid.Tape n u U) : Within (machine w) ((innerSpacePolynomial w).eval word.length) U := by
  have hs := row_prefix_space (machine w) _ mid.var mid.Tape n u U hp _ (prefix_space w word instructions mid htrace)
  have hn := (row_prefix_cost (machine w) _ mid.var mid.Tape n u U hp).trans
    (TapeSimulation.row_budget (machine w) bit l mid.var mid.Tape)
  rw [inner_space_eval]
  exact within_mono (machine w) _ _ _ hs (Nat.add_le_add_left hn _)

/-- Absolute head position of every actual primitive pre. Only actual
move instructions change this sum; a bundled TM1 row is never charged as
one primitive. Thus the visited cells obey the same bound. -/
theorem prefix_inner_shift (word : List Bool) (instructions : List (Option Bool))
    (mid : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) mid)
    (l : TapeSimulation.Label (machine w)) (bit : Bool)
    (n : ℕ) (u : (machine w).core.σ) (U : Tape (TapeSimulation.Alphabet (machine w)))
    (hp : RowPrefix (machine w)
      (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
      mid.var mid.Tape n u U) :
    let δ := instructionShift (machine w) instructions (PathSegmentation.start w word)+primitiveShift (machine w) n
      (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
      mid.var mid.Tape;
    -(↑((visitedPolynomial w).eval word.length) : ℤ) ≤ δ ∧ δ ≤ (↑((visitedPolynomial w).eval word.length) : ℤ) := by
  have hs := prefix_shift w word instructions mid htrace
  have hm := primitive_shift_bound (machine w) n
    (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
    mid.var mid.Tape
  have hn := (row_prefix_cost (machine w) _ mid.var mid.Tape n u U hp).trans
    (TapeSimulation.row_budget (machine w) bit l mid.var mid.Tape)
  rw [visited_eval]
  dsimp only
  push_cast
  omega

theorem prefix_inner_absolute_space (word : List Bool) (instructions : List (Option Bool))
    (mid : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) mid)
    (l : TapeSimulation.Label (machine w)) (bit : Bool)
    (n : ℕ) (u : (machine w).core.σ) (U : Tape (TapeSimulation.Alphabet (machine w)))
    (hp : RowPrefix (machine w)
      (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
      mid.var mid.Tape n u U) :
    ∀ i : ℤ,
      let δ := (instructionShift (machine w) instructions (PathSegmentation.start w word) +
        primitiveShift (machine w) n
          (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
          mid.var mid.Tape)
      let R := (↑((absoluteSpacePolynomial w).eval word.length) : ℤ)
      i+δ < -R ∨ R < i+δ → U.nth i = default := by
  have hs := prefix_inner_space w word instructions mid htrace l bit n u U hp
  have hm := prefix_inner_shift w word instructions mid htrace l bit n u U hp
  rw [inner_space_eval,space_eval] at hs
  rw [visited_eval] at hm
  intro i
  dsimp only
  intro hi
  rw [absolute_space_eval] at hi
  apply hs i
  dsimp only at hm hi
  push_cast at hm hi ⊢
  omega

/-- Each genuinely visited primitive head position has a literal index in
the SAME finite interval of 2*V(N)+1 cells; no visited-set size is assumed. -/
theorem prefix_inner_visited (word : List Bool) (instructions : List (Option Bool))
    (mid : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) mid)
    (l : TapeSimulation.Label (machine w)) (bit : Bool)
    (n : ℕ) (u : (machine w).core.σ) (U : Tape (TapeSimulation.Alphabet (machine w)))
    (hp : RowPrefix (machine w)
      (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
      mid.var mid.Tape n u U) :
    ∃ i : Fin (2*(visitedPolynomial w).eval word.length+1),
      (i.val : ℤ)-(↑((visitedPolynomial w).eval word.length) : ℤ) =
        instructionShift (machine w) instructions (PathSegmentation.start w word)+primitiveShift (machine w) n
          (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
          mid.var mid.Tape :=
  bounded_position _ _ (prefix_inner_shift w word instructions mid htrace l bit n u U hp)

/-- Actual binary snapshot lengths for every primitive configuration. The
finite symbol/control/state codes are fixed internally and faithful; no
free storage bound or mathematical decoder is a physical opcode. -/
theorem prefix_inner_storage_bits (word : List Bool) (instructions : List (Option Bool))
    (mid : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) mid)
    (l : TapeSimulation.Label (machine w)) (bit : Bool)
    (n : ℕ) (u : (machine w).core.σ) (U : Tape (TapeSimulation.Alphabet (machine w)))
    (hp : RowPrefix (machine w)
      (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
      mid.var mid.Tape n u U) (control : Option (TapeSimulation.Label (machine w))) :
    Within (machine w) ((innerSpacePolynomial w).eval word.length) U ∧
    (snapshot (machine w) ((innerSpacePolynomial w).eval word.length) ⟨control,u,U⟩).length ≤
      (storageBitsPolynomial w).eval word.length := by
  refine ⟨prefix_inner_space w word instructions mid htrace l bit n u U hp,?_⟩
  rw [snapshot_length,storage_bits_eval]

theorem prefix_storage_bits (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint) :
    Within (machine w) ((innerSpacePolynomial w).eval word.length) endpoint.Tape ∧
    (snapshot (machine w) ((innerSpacePolynomial w).eval word.length) endpoint).length ≤
      (storageBitsPolynomial w).eval word.length := by
  refine ⟨?_,?_⟩
  · apply within_mono (machine w) _ _ _ (prefix_space w word instructions endpoint htrace)
    rw [inner_space_eval]
    exact Nat.le_add_right _ _
  · rw [snapshot_length,storage_bits_eval]

theorem prefix_primitive_storage_bits (word : List Bool) (instructions : List (Option Bool))
    (mid : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) mid)
    (l : TapeSimulation.Label (machine w)) (bit : Bool)
    (n : ℕ) (u : (machine w).core.σ) (U : Tape (TapeSimulation.Alphabet (machine w)))
    (hp : RowPrefix (machine w)
      (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
      mid.var mid.Tape n u U) (control : Option (TapeSimulation.Label (machine w))) :
    Within (machine w) ((innerSpacePolynomial w).eval word.length) U ∧
    (primitiveSnapshot (machine w) ((innerSpacePolynomial w).eval word.length) bit l n mid.var mid.Tape
      ⟨control,u,U⟩).length ≤ (primitiveStorageBitsPolynomial w).eval word.length := by
  refine ⟨prefix_inner_space w word instructions mid htrace l bit n u U hp,?_⟩
  rw [primitive_snapshot_length]
  simp [primitiveStorageBitsPolynomial,storageBitsPolynomial,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

/-- Sole all-raw trajectory consumer of this SAME source: no new witness or
machine representation is introduced. Every actual finite pre is bounded,
extends to real halt, and carries a faithful polynomial binary tape snapshot. -/
theorem total_source (word : List Bool) (instructions : List (Option Bool))
    (endpoint : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint) :
    instructions.length ≤ (microPolynomial w).eval word.length ∧
    TapeSimulation.instructionOperations (machine w) instructions (PathSegmentation.start w word) ≤
      (microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) ∧
    (∃ rest final, TapeSimulation.InstructionTrace (machine w) rest endpoint final ∧ final.l = none ∧
      (instructions++rest).length ≤ (microPolynomial w).eval word.length) ∧
    Within (machine w) ((innerSpacePolynomial w).eval word.length) endpoint.Tape ∧
    (snapshot (machine w) ((innerSpacePolynomial w).eval word.length) endpoint).length ≤
      (storageBitsPolynomial w).eval word.length :=
  ⟨prefix_time w word instructions endpoint htrace,prefix_primitive w word instructions endpoint htrace,
    prefix_completion w word instructions endpoint htrace,(prefix_storage_bits w word instructions endpoint htrace).1,
    (prefix_storage_bits w word instructions endpoint htrace).2⟩

/-- Every actual instruction pre of an arbitrary halting computation,
including rejecting input, has a whole-tape polynomial support window. -/
theorem halted_prefix_space (word : List Bool) (instructions left right : List (Option Bool))
    (endpoint mid : FiniteCfg (machine w))
    (htrace : TapeSimulation.InstructionTrace (machine w) instructions (PathSegmentation.start w word) endpoint)
    (hhalt : endpoint.l = none) (hcut : instructions = left++right)
    (hprefix : TapeSimulation.InstructionTrace (machine w) left (PathSegmentation.start w word) mid) :
    Within (machine w) ((spacePolynomial w).eval word.length) mid.Tape := by
  have hlen : left.length ≤ (microPolynomial w).eval word.length := by
    have hall := halted_time w word instructions endpoint htrace hhalt
    rw [hcut,List.length_append] at hall
    omega
  have hs := instruction_space (machine w) left _ mid hprefix word.length (initial_space w word)
  rw [space_eval]
  exact within_mono (machine w) _ _ _ hs
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) word.length)

theorem physical_prefix_space (word : List Bool) (p : PathSegmentation.PhysicalPath w word)
    (left right : List (Option Bool)) (mid : FiniteCfg (machine w))
    (hcut : p.val = left++right)
    (hprefix : TapeSimulation.InstructionTrace (machine w) left (PathSegmentation.start w word) mid) :
    Within (machine w) ((spacePolynomial w).eval word.length) mid.Tape := by
  obtain ⟨endpoint,he,hr⟩ := p.property
  exact halted_prefix_space w word p.val left right endpoint mid hr
    (TapeSimulation.accepting_endpoint_halts w endpoint he) hcut hprefix

/-- Head displacement is the signed sum of the actual move instructions in
the observed pre, using the actual read/write/test state at every row. -/
theorem physical_prefix_shift (word : List Bool) (p : PathSegmentation.PhysicalPath w word)
    (left right : List (Option Bool)) (mid : FiniteCfg (machine w))
    (hcut : p.val = left++right)
    (hprefix : TapeSimulation.InstructionTrace (machine w) left (PathSegmentation.start w word) mid) :
    -((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) ≤
      instructionShift (machine w) left (PathSegmentation.start w word) ∧
    instructionShift (machine w) left (PathSegmentation.start w word) ≤
      ((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) := by
  have hs := instruction_shift_bound (machine w) left _ mid hprefix
  have hn : left.length ≤ (microPolynomial w).eval word.length := by
    have hh := physical_time w word p
    rw [hcut,List.length_append] at hh
    omega
  have hm : (left.length*TapeSimulation.rowBudget (machine w) : ℤ) ≤
      ((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_right (TapeSimulation.rowBudget (machine w)) hn
  exact ⟨(neg_le_neg hm).trans hs.1,hs.2.trans hm⟩

/-- All nonblank cells, expressed in the original input's coordinates using
the actual signed move sum, lie in this polynomial window. -/
theorem physical_absolute_space (word : List Bool) (p : PathSegmentation.PhysicalPath w word)
    (left right : List (Option Bool)) (mid : FiniteCfg (machine w))
    (hcut : p.val = left++right)
    (hprefix : TapeSimulation.InstructionTrace (machine w) left (PathSegmentation.start w word) mid) :
    ∀ i : ℤ, let δ := instructionShift (machine w) left (PathSegmentation.start w word);
      let R := (word.length : ℤ)+2*((microPolynomial w).eval word.length*TapeSimulation.rowBudget (machine w) : ℤ);
      i+δ < -R ∨ R < i+δ → mid.Tape.nth i = default := by
  have hs := physical_prefix_space w word p left right mid hcut hprefix
  have hm := physical_prefix_shift w word p left right mid hcut hprefix
  rw [space_eval] at hs
  intro i
  dsimp only
  intro hi
  apply hs i
  push_cast
  try dsimp only at hi
  push_cast at hi
  omega

theorem physical_inner_space (word : List Bool) (p : PathSegmentation.PhysicalPath w word)
    (left right : List (Option Bool)) (mid : FiniteCfg (machine w))
    (hcut : p.val = left++right)
    (hprefix : TapeSimulation.InstructionTrace (machine w) left (PathSegmentation.start w word) mid)
    (l : TapeSimulation.Label (machine w)) (hl : mid.l = some l) (bit : Bool)
    (n : ℕ) (u : (machine w).core.σ) (U : Tape (TapeSimulation.Alphabet (machine w)))
    (hp : RowPrefix (machine w)
      (if bit then (TapeSimulation.programme (machine w)).alternate l else (TapeSimulation.programme (machine w)).core l)
      mid.var mid.Tape n u U) :
    Within (machine w) ((spacePolynomial w).eval word.length+TapeSimulation.rowBudget (machine w)) U := by
  have hspace := physical_prefix_space w word p left right mid hcut hprefix
  have hs := row_prefix_space (machine w) _ mid.var mid.Tape n u U hp _ hspace
  have hcost := (row_prefix_cost (machine w) _ mid.var mid.Tape n u U hp).trans
    (TapeSimulation.row_budget (machine w) bit l mid.var mid.Tape)
  exact within_mono (machine w) _ _ _ hs (Nat.add_le_add_left hcost _)

/-- One consumer joins the already proved SAME-path count bijection to the
new measured clock and primitive resource bounds. No machine, path budget,
decoder success or count-preservation law is an extra source premise. -/
theorem witness_source (a : α) :
    Nonempty (ConventionalSharpPSource.AcceptedWitness w a ≃
      PathSegmentation.PhysicalPath w (TotalRawSource.encodedInput w a)) ∧
    PathSegmentation.count w (TotalRawSource.encodedInput w a) = f a ∧
    ∀ p : PathSegmentation.PhysicalPath w (TotalRawSource.encodedInput w a),
      p.val.length ≤ (microPolynomial w).eval (TotalRawSource.encodedInput w a).length ∧
      TapeSimulation.instructionOperations (machine w) p.val
        (PathSegmentation.start w (TotalRawSource.encodedInput w a)) ≤
        (microPolynomial w).eval (TotalRawSource.encodedInput w a).length*TapeSimulation.rowBudget (machine w) :=
  ⟨(PathSegmentation.witness_source w a).1,(PathSegmentation.witness_source w a).2,
    fun p => ⟨physical_time w _ p,physical_primitive w _ p⟩⟩

/-- No caller capacity/clock budget: an arbitrary legal source pre supplies
the current stacks, and all_path_resources internally supplies their bound. -/
theorem boundary_scanner (word : List Bool) (tokens : List (Option Bool)) (c : (machine w).Config)
    (htrace : (machine w).TraceValid tokens (initList (machine w).core word) c)
    (L : Columns (machine w))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((c.stk k).map some).reverse)
    (k : (machine w).core.K)
    (o : TM2to1.StAct (machine w).core.K (machine w).core.Γ (machine w).core.σ k)
    (q : (machine w).core.Stmt) :
    ∃ L' : Columns (machine w),
      Rows (machine w) ((c.stk k).length+1+(TM2to1.stWrite c.var (c.stk k) o).length)
        (go (machine w) k o q c.var L 0) (ret (machine w) q (TM2to1.stVar c.var (c.stk k) o) L' 0) ∧
      (c.stk k).length+1+(TM2to1.stWrite c.var (c.stk k) o).length ≤
        2*(TotalRawSource.capacityPolynomial w).eval word.length+2 ∧
      Span (machine w) L ((TotalRawSource.capacityPolynomial w).eval word.length) ∧
      Span (machine w) L' ((TotalRawSource.capacityPolynomial w).eval word.length+1) := by
  have hB := source_capacity w word tokens c htrace
  obtain ⟨L',hr,hspan,hspan',hgo,hret⟩ := round_space (machine w) k o q c.var c.stk L hL _ hB
  exact ⟨L',hr,round_bound (machine w) k o c.var c.stk _ hB,hspan,hspan'⟩

/-- Actual finite instruction transcript of the round. a is an existing
finite-table scanner configuration; the equality states its literal frame,
not a caller simulator or a time bound. Finite support is consumed by the
old finite_step_lift at every actual row. -/
theorem boundary_finite_round (word : List Bool) (tokens : List (Option Bool)) (c : (machine w).Config)
    (htrace : (machine w).TraceValid tokens (initList (machine w).core word) c)
    (L : Columns (machine w))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((c.stk k).map some).reverse)
    (k : (machine w).core.K)
    (o : TM2to1.StAct (machine w).core.K (machine w).core.Γ (machine w).core.σ k)
    (q : (machine w).core.Stmt) (a : FiniteCfg (machine w))
    (ha : TapeSimulation.forget (machine w) a = go (machine w) k o q c.var L 0) :
    ∃ b : FiniteCfg (machine w), ∃ L' : Columns (machine w),
      TapeSimulation.InstructionTrace (machine w)
        (List.replicate ((c.stk k).length+1+(TM2to1.stWrite c.var (c.stk k) o).length) none) a b ∧
      TapeSimulation.forget (machine w) b = ret (machine w) q (TM2to1.stVar c.var (c.stk k) o) L' 0 ∧
      (List.replicate ((c.stk k).length+1+(TM2to1.stWrite c.var (c.stk k) o).length)
        (none : Option Bool)).length ≤ 2*(TotalRawSource.capacityPolynomial w).eval word.length+2 ∧
      TapeSimulation.instructionOperations (machine w)
        (List.replicate ((c.stk k).length+1+(TM2to1.stWrite c.var (c.stk k) o).length) none) a ≤
          (2*(TotalRawSource.capacityPolynomial w).eval word.length+2)*TapeSimulation.rowBudget (machine w) := by
  obtain ⟨L',hr,hlen,hspan,hspan'⟩ := boundary_scanner w word tokens c htrace L hL k o q
  obtain ⟨b,hb,htrace'⟩ := rows_finite (machine w) _ a _ (ha.symm ▸ hr)
  have hcost := TapeSimulation.instruction_operations_le (machine w) _ a b htrace'
  simp only [List.length_replicate] at hcost
  exact ⟨b,L',htrace',hb,by simpa only [List.length_replicate] using hlen,
    hcost.trans (Nat.mul_le_mul_right (TapeSimulation.rowBudget (machine w)) hlen)⟩

end Witness

/- prefix_completion derives genuine halt extensions for arbitrary actual
unfinished instruction words from the old ALL-raw source run, without a halt
premise. prefix_time and prefix_deadline give a uniform physical clock;
source_prefix_segmentation produces complete original rows and at most one
unfinished deterministic interior interval. Primitive motion and support are
bounded even inside empty peek's temporary left move. Binary snapshots include
actual finite labels/registers/cells and the residual-PC subterm closure of the
same two installed tables. These are resource receipts, not a newly installed
runtime encoder. The whole conventional ND TM0 dispatcher and raw-input tape
frontend remain independent obligations; no conventional #P equivalence is
asserted here. Original source and accepting-path counts are unchanged. -/
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TapeMicrostepBudget
