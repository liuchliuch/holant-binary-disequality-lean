import Holant.Proofs.CountingMachines.StandardMachine.Support.PathSegmentationCore

set_option backward.isDefEq.respectTransparency false
/-!
Adapted reference proof. See the task validation reports. Concrete clocked go/action/ret scanner rounds of the SAME
finite TM1 table. Counts below are lengths of actual None-row instruction
traces, constructed by induction from the installed move/write code; no
Nat.find, Reaches observer clock or caller microstep budget is used.

Clocked syntax induction includes ret-bottom continuations and frame updates.
Actual source paths produce instruction words with measured lengths. Every
unfinished physical pre is internally segmented into completed rows and at
most one unfinished interval, and extends to an actual all-raw halting source
run within the same derived polynomial. Actual primitive movement, tape support
and faithful finite control/state/cell bit snapshots have polynomial bounds;
the complete conventional ND TM0/frontend model bridge remains separate.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TapeMicrostepBudget
open Turing Computability Holant.Complexity StateTransition Relation
variable (m : BinaryMachine)

abbrev Columns := ListBlank (∀ k, Option (m.core.Γ k))
abbrev RawCfg := TapeSimulation.Cfg m
abbrev FiniteCfg := TapeSimulation.FiniteCfg m

def bottom (L : Columns m) : Tape (TapeSimulation.Alphabet m) := Tape.mk' ∅ (TM2to1.addBottom L)
def positionTape (L : Columns m) (n : ℕ) : Tape (TapeSimulation.Alphabet m) := (Tape.move Dir.right)^[n] (bottom m L)
def go (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (q : m.core.Stmt) (v : m.core.σ) (L : Columns m) (n : ℕ) : RawCfg m :=
  ⟨some (.go k o q),v,positionTape m L n⟩
def ret (q : m.core.Stmt) (v : m.core.σ) (L : Columns m) (n : ℕ) : RawCfg m :=
  ⟨some (.ret q),v,positionTape m L n⟩

/-- Exact physical row count, with no real halt self-edge. -/
def Rows : ℕ → RawCfg m → RawCfg m → Prop
  | 0,a,b => a = b
  | n+1,a,b => ∃ next, TapeSimulation.step m none a = some next ∧ Rows n next b

theorem rows_append (n k : ℕ) (a mid b : RawCfg m)
    (hn : Rows m n a mid) (hk : Rows m k mid b) : Rows m (n+k) a b := by
  induction n generalizing a with
  | zero => subst a; simpa only [Nat.zero_add] using hk
  | succ n ih =>
      rw [Nat.succ_add]
      obtain ⟨next,hs,hr⟩ := hn
      exact ⟨next,hs,ih next hr⟩

theorem rows_finite (n : ℕ) (a : FiniteCfg m) (b : RawCfg m)
    (h : Rows m n (TapeSimulation.forget m a) b) :
    ∃ c : FiniteCfg m, TapeSimulation.forget m c = b ∧
      TapeSimulation.InstructionTrace m (List.replicate n none) a c := by
  induction n generalizing a with
  | zero => exact ⟨a,h,rfl⟩
  | succ n ih =>
      obtain ⟨next,hs,hr⟩ := h
      obtain ⟨next',hs',he⟩ := TapeSimulation.finite_step_lift m none a next hs
      obtain ⟨b',hb,htrace⟩ := ih next' (he.symm ▸ hr)
      exact ⟨b',hb,next',hs',htrace⟩

theorem head_columns (L : Columns m) (n : ℕ) :
    (positionTape m L n).head.2 = L.nth n := by
  rw [positionTape,Tape.move_right_n_head,bottom,Tape.mk'_nth_nat,TM2to1.addBottom_nth_snd]

theorem head_marker (L : Columns m) (n : ℕ) : (positionTape m L n).head.1 = decide (n = 0) := by
  rw [positionTape,Tape.move_right_n_head,bottom,Tape.mk'_nth_nat]
  cases n with
  | zero => simpa only [ListBlank.nth_zero,decide_true] using TM2to1.addBottom_head_fst L
  | succ n => simpa using TM2to1.addBottom_nth_succ_fst L n

def markerMap : PointedMap (TapeSimulation.Alphabet m) Bool := ⟨Prod.fst,rfl⟩

/-- Every actual push/pop write keeps the stored bottom bit unchanged,
at every cell; this is stronger than just preserving the current head bit. -/
theorem write_marker (T : Tape (TapeSimulation.Alphabet m)) (row : ∀ k, Option (m.core.Γ k)) :
    (T.write (T.head.1,row)).map (markerMap m) = T.map (markerMap m) := by
  rw [Tape.map_write]
  simpa [markerMap] using Tape.write_self (T.map (markerMap m))

theorem read_present (k : m.core.K) (S : List (m.core.Γ k)) (L : Columns m)
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n : ℕ) (hn : n < S.length) :
    ((positionTape m L n).head.2 k).isNone = false := by
  rw [head_columns,TM2to1.stk_nth_val n hL,List.getElem?_eq_getElem]
  · rfl
  · simpa only [List.length_reverse] using hn

theorem read_end (k : m.core.K) (S : List (m.core.Γ k)) (L : Columns m)
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) :
    ((positionTape m L S.length).head.2 k).isNone = true := by
  rw [head_columns,TM2to1.stk_nth_val _ hL,List.getElem?_eq_none]
  · rfl
  · simp

theorem go_step (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (q : m.core.Stmt) (v : m.core.σ) (S : List (m.core.Γ k)) (L : Columns m)
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n : ℕ) (hn : n < S.length) :
    TapeSimulation.step m none (go m k o q v L n) = some (go m k o q v L (n+1)) := by
  have hread := read_present m k S L hL n hn
  simp only [go,TapeSimulation.step,TapeSimulation.split,TapeSimulation.program,TM2to1.tr,
    TM1.stepAux,hread,Bool.false_eq_true,ite_false,Bool.cond_false]
  simp only [positionTape,Function.iterate_succ_apply']

/-- Exactly n go rows, not merely an unclocked reachability assertion. -/
theorem go_rows (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (q : m.core.Stmt) (v : m.core.σ) (S : List (m.core.Γ k)) (L : Columns m)
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n : ℕ) (hn : n ≤ S.length) :
    Rows m n (go m k o q v L 0) (go m k o q v L n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hpre := ih (by omega)
      exact rows_append m n 1 _ _ _ hpre
        ⟨_,go_step m k o q v S L hL n (by omega),rfl⟩

theorem ret_step (q : m.core.Stmt) (v : m.core.σ) (L : Columns m) (n : ℕ) :
    TapeSimulation.step m none (ret m q v L (n+1)) = some (ret m q v L n) := by
  have hmarker : (positionTape m L (n+1)).head.1 = false := by simp [head_marker]
  simp only [ret,TapeSimulation.step,TapeSimulation.split,TapeSimulation.program,TM2to1.tr,
    TM1.stepAux,hmarker,Bool.false_eq_true,ite_false,Bool.cond_false]
  simp only [positionTape,Function.iterate_succ_apply',Tape.move_right_left]

/-- Exactly n return rows; row n+1 at bottom runs trNormal q and is NOT
silently included as another scan row or another source choice. -/
theorem ret_rows (q : m.core.Stmt) (v : m.core.σ) (L : Columns m) (n : ℕ) :
    Rows m n (ret m q v L n) (ret m q v L 0) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨_,ret_step m q v L n,ih⟩

def actionStacks (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) : ∀ k, List (m.core.Γ k) :=
  Function.update S k (TM2to1.stWrite v (S k) o)

theorem action_length (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) :
    (TM2to1.stWrite v (S k) o).length ≤ (S k).length+1 := by
  cases o <;> simp [TM2to1.stWrite] <;> omega

theorem action_capacity (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) (B : ℕ) (hB : ∀ k, (S k).length ≤ B) :
    ∀ j, (actionStacks m k o v S j).length ≤ B+1 := by
  intro j
  by_cases hj : j = k
  · subst j
    simp only [actionStacks,Function.update_self]
    exact (action_length m k o v S).trans (Nat.add_le_add_right (hB k) 1)
  · simp only [actionStacks,Function.update_of_ne hj]
    exact (hB j).trans (Nat.le_add_right _ _)

theorem action_step (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (q : m.core.Stmt) (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) (L : Columns m)
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    ∃ L' : Columns m,
      (∀ j, L'.map (proj j) = ListBlank.mk ((actionStacks m k o v S j).map some).reverse) ∧
      TapeSimulation.step m none (go m k o q v L (S k).length) =
        some (ret m q (TM2to1.stVar v (S k) o) L' (TM2to1.stWrite v (S k) o).length) := by
  obtain ⟨L',hL',hactual⟩ := TM2to1.tr_respects_aux₂
    (q := TM1.Stmt.goto (fun _ _ => TM2to1.Λ'.ret q)) hL o
  refine ⟨L',hL',?_⟩
  have hread := read_end m k (S k) L (hL k)
  simp only [go,TapeSimulation.step,TapeSimulation.split,TapeSimulation.program,TM2to1.tr,
    TM1.stepAux,hread,Bool.false_eq_true,ite_false,Bool.cond_true]
  change some (TM1.stepAux (TM2to1.trStAct (TM1.Stmt.goto (fun _ _ => TM2to1.Λ'.ret q)) o)
    v (positionTape m L (S k).length)) = _
  dsimp only [positionTape, bottom]
  rw [hactual]
  simp only [ret,positionTape,bottom,TM1.stepAux,Function.update_self]

/-- Concrete scanner/action round. Its physical fee is oldLength+1+newLength,
including the actual terminating go write/read row and all return rows. -/
theorem action_round (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (q : m.core.Stmt) (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) (L : Columns m)
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    ∃ L' : Columns m,
      (∀ j, L'.map (proj j) = ListBlank.mk ((actionStacks m k o v S j).map some).reverse) ∧
      Rows m ((S k).length+1+(TM2to1.stWrite v (S k) o).length)
        (go m k o q v L 0) (ret m q (TM2to1.stVar v (S k) o) L' 0) := by
  obtain ⟨L',hL',hstep⟩ := action_step m k o q v S L hL
  refine ⟨L',hL',?_⟩
  have hgo := go_rows m k o q v (S k) L (hL k) (S k).length le_rfl
  have haction : Rows m 1 _ _ := ⟨_,hstep,rfl⟩
  exact rows_append m _ _ _ _ _ (rows_append m _ 1 _ _ _ hgo haction)
    (ret_rows m q (TM2to1.stVar v (S k) o) L' _)

theorem round_bound (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) (B : ℕ) (hB : ∀ k, (S k).length ≤ B) :
    (S k).length+1+(TM2to1.stWrite v (S k) o).length ≤ 2*B+2 := by
  have hnew := action_length m k o v S
  have hold := hB k
  omega

def actions : m.core.Stmt → ℕ
  | .push _ _ q => actions q+1
  | .pop _ _ q => actions q+1
  | .peek _ _ q => actions q+1
  | .load _ q => actions q
  | .branch _ q r => actions q+actions r
  | .goto _ => 0
  | .halt => 0

theorem actions_run (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (q : m.core.Stmt) : actions m (TM2to1.stRun o q) = actions m q+1 := by cases o <;> rfl

def statementBound (q : m.core.Stmt) (B : ℕ) : ℕ := actions m q*(2*(B+actions m q)+3)

theorem statement_bound_mono (a b B : ℕ) (h : a ≤ b) :
    a*(2*(B+a)+3) ≤ b*(2*(B+b)+3) := by
  exact Nat.mul_le_mul h (by omega)

theorem ret_bottom (q : m.core.Stmt) (v : m.core.σ) (L : Columns m) :
    TapeSimulation.step m none (ret m q v L 0) =
      some (TM1.stepAux (TM2to1.trNormal q) v (bottom m L)) := by
  simp [ret,positionTape,TapeSimulation.step,TapeSimulation.split,TapeSimulation.program,
    TM2to1.tr,TM1.stepAux,bottom,Tape.mk'_head,TM2to1.addBottom_head_fst]

/-- Clocked syntax induction after the FIRST normal/return row has evaluated
trNormal q. Each stack action includes its return-at-bottom continuation row;
loads and tests are exactly the operations bundled in that real TM1 row. -/
theorem statement_rows (q : m.core.Stmt) (v : m.core.σ)
    (S : ∀ k, List (m.core.Γ k)) (L : Columns m)
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (B : ℕ) (hB : ∀ k, (S k).length ≤ B) :
    ∃ n : ℕ, ∃ b : RawCfg m, TapeSimulation.Encoded m (TM2.stepAux q v S) b ∧
      Rows m n (TM1.stepAux (TM2to1.trNormal q) v (bottom m L)) b ∧ n ≤ statementBound m q B := by
  induction q using TM2to1.stmtStRec generalizing v S L hL B hB with
  | run k o q ih =>
      obtain ⟨L',hL',hr⟩ := action_round m k o q v S L hL
      have hnew := action_capacity m k o v S B hB
      obtain ⟨n,b,hb,hn,hbudget⟩ := ih (TM2to1.stVar v (S k) o) (actionStacks m k o v S)
        L' hL' (B+1) hnew
      let r := (S k).length+1+(TM2to1.stWrite v (S k) o).length
      refine ⟨r+1+n,b,?_,?_,?_⟩
      · simpa only [TM2to1.step_run,actionStacks] using hb
      · have hcontinue : Rows m 1 (ret m q (TM2to1.stVar v (S k) o) L' 0)
            (TM1.stepAux (TM2to1.trNormal q) (TM2to1.stVar v (S k) o) (bottom m L')) :=
          ⟨_,ret_bottom m q _ L',rfl⟩
        have hall := rows_append m (r+1) n _ _ _ (rows_append m r 1 _ _ _ hr hcontinue) hn
        simpa only [TM2to1.trNormal_run,TM1.stepAux,go,positionTape,Function.iterate_zero_apply] using hall
      · have hrbound : r+1 ≤ 2*B+3 := by
          have := round_bound m k o v S B hB
          dsimp [r]; omega
        let D := 2*(B+1+actions m q)+3
        have hnb : n ≤ actions m q*D := by simpa [statementBound,D,Nat.add_assoc] using hbudget
        calc
          r+1+n ≤ (2*B+3)+actions m q*D := Nat.add_le_add hrbound hnb
          _ ≤ D+actions m q*D := Nat.add_le_add_right (by dsimp [D]; omega) _
          _ = statementBound m (TM2to1.stRun o q) B := by
            rw [statementBound,actions_run]
            dsimp [D]
            ring
  | load f q ih =>
      simpa only [TM2.stepAux,TM2to1.trNormal,TM1.stepAux,statementBound,actions]
        using (ih (f v) S L hL B hB)
  | branch f q r ihq ihr =>
      cases hf : f v with
      | false =>
          obtain ⟨n,b,hb,hn,hbudget⟩ := ihr v S L hL B hB
          refine ⟨n,b,?_,?_,?_⟩
          · simpa only [TM2.stepAux,hf,Bool.cond_false] using hb
          · simpa only [TM2to1.trNormal,TM1.stepAux,hf,Bool.cond_false] using hn
          · exact hbudget.trans (statement_bound_mono _ _ B (Nat.le_add_left _ _))
      | true =>
          obtain ⟨n,b,hb,hn,hbudget⟩ := ihq v S L hL B hB
          refine ⟨n,b,?_,?_,?_⟩
          · simpa only [TM2.stepAux,hf,Bool.cond_true] using hb
          · simpa only [TM2to1.trNormal,TM1.stepAux,hf,Bool.cond_true] using hn
          · exact hbudget.trans (statement_bound_mono _ _ B (Nat.le_add_right _ _))
  | goto f => exact ⟨0,_,TM2to1.TrCfg.mk L hL,rfl,by simp [statementBound,actions]⟩
  | halt => exact ⟨0,_,TM2to1.TrCfg.mk L hL,rfl,by simp [statementBound,actions]⟩

local instance : Fintype m.core.Λ := m.core.ΛFin
open scoped BigOperators
def actionBudget : ℕ := ∑ l : m.core.Λ, (actions m (m.core.m l)+actions m (m.alternate l))

theorem selected_actions (bit : Bool) (l : m.core.Λ) :
    actions m (TapeSimulation.selected m bit l) ≤ actionBudget m := by
  classical
  have hs : actions m (m.core.m l)+actions m (m.alternate l) ≤ actionBudget m :=
    by
      unfold actionBudget
      exact Finset.single_le_sum (f := fun key => actions m (m.core.m key) + actions m (m.alternate key)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  cases bit
  · exact (Nat.le_add_right _ _).trans hs
  · exact (Nat.le_add_left _ _).trans hs

def rowBound (B : ℕ) : ℕ := 1+actionBudget m*(2*(B+actionBudget m)+3)

theorem selected_statement_bound (bit : Bool) (l : m.core.Λ) (B : ℕ) :
    1+statementBound m (TapeSimulation.selected m bit l) B ≤ rowBound m B :=
  Nat.add_le_add_left (statement_bound_mono _ _ B (selected_actions m bit l)) 1

theorem source_edge (token : Option Bool) (c d : m.Config) (a : FiniteCfg m)
    (h : m.step token c = some d) (he : TapeSimulation.Encoded m c (TapeSimulation.forget m a))
    (B : ℕ) (hB : ∀ k, (c.stk k).length ≤ B) :
    ∃ b : FiniteCfg m, ∃ instructions : List (Option Bool),
      TapeSimulation.Encoded m d (TapeSimulation.forget m b) ∧
      TapeSimulation.InstructionTrace m instructions a b ∧
      instructions.filterMap id = token.toList ∧ instructions.length ≤ rowBound m B := by
  generalize hraw : TapeSimulation.forget m a = raw at he
  cases he with
  | @mk label v S L hL =>
      cases label with
      | none =>
          cases token with
          | some bit => simp [BinaryMachine.step] at h
          | none =>
              have hd : (⟨none,v,S⟩ : m.Config) = d := Option.some.inj h
              refine ⟨a,[],?_,rfl,rfl,by simp [rowBound]⟩
              exact hraw.symm ▸ (hd ▸ TM2to1.TrCfg.mk L hL)
      | some l =>
          have chosen (bit : Bool) (hq : TM2.stepAux (TapeSimulation.selected m bit l) v S = d)
              (hfirst : TapeSimulation.step m token (TapeSimulation.forget m a) =
                some (TM1.stepAux (TM2to1.trNormal (TapeSimulation.selected m bit l)) v (bottom m L))) :
              ∃ b : FiniteCfg m, ∃ instructions : List (Option Bool),
                TapeSimulation.Encoded m d (TapeSimulation.forget m b) ∧
                TapeSimulation.InstructionTrace m instructions a b ∧
                instructions.filterMap id = token.toList ∧ instructions.length ≤ rowBound m B := by
            obtain ⟨n,endpoint,hend,hr,hnb⟩ := statement_rows m (TapeSimulation.selected m bit l) v S L hL B hB
            obtain ⟨first,hf,he⟩ := TapeSimulation.finite_step_lift m token a _ hfirst
            obtain ⟨b,hend',hrows⟩ := rows_finite m n first endpoint (he.symm ▸ hr)
            refine ⟨b,token::List.replicate n none,?_,⟨first,hf,hrows⟩,?_,?_⟩
            · exact hend'.symm ▸ (hq ▸ hend)
            · cases token <;> simp
            · simpa only [List.length_cons,List.length_replicate,Nat.add_comm] using
                (Nat.add_le_add_left hnb 1).trans (selected_statement_bound m bit l B)
          cases token with
          | none =>
              cases hs : m.split l with
              | true => simp [BinaryMachine.step,hs] at h
              | false =>
                  apply chosen false (Option.some.inj (by simpa [BinaryMachine.step,TapeSimulation.selected,hs,ite_apply] using h))
                  rw [hraw]
                  simp [TapeSimulation.step,TapeSimulation.split,TapeSimulation.program,TM2to1.tr,hs,bottom]
          | some bit =>
              cases hs : m.split l with
              | false => simp [BinaryMachine.step,hs] at h
              | true =>
                  apply chosen bit (Option.some.inj (by simpa [BinaryMachine.step,TapeSimulation.selected,hs,ite_apply] using h))
                  rw [hraw]
                  simp [TapeSimulation.step,TapeSimulation.split,TapeSimulation.program,TM2to1.tr,hs,bottom]

def Span (L : Columns m) (B : ℕ) : Prop :=
  ∀ n, B+1 ≤ n → (TM2to1.addBottom L).nth n = default

theorem columns_span (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) (L : Columns m)
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (B : ℕ) (hB : ∀ k, (S k).length ≤ B) : Span m L B := by
  intro n hn
  have he : TapeSimulation.Encoded m (⟨none,v,S⟩ : m.Config)
      (⟨none,v,bottom m L⟩ : RawCfg m) := TM2to1.TrCfg.mk L hL
  simpa only [bottom,Tape.mk'_right₀] using
    TapeSimulation.encoded_cells m _ _ he B hB n hn

theorem bottom_blank (L : Columns m) (B : ℕ) (hB : Span m L B) (i : ℤ)
    (hi : i < 0 ∨ (B : ℤ) < i) : (bottom m L).nth i = default := by
  cases i with
  | ofNat n =>
      change (bottom m L).nth (n : ℤ) = default
      rw [bottom,Tape.mk'_nth_nat]
      have hi' : (n : ℤ) < 0 ∨ (B : ℤ) < (n : ℤ) := hi
      exact hB n (by omega)
  | negSucc n =>
      change (∅ : ListBlank (TapeSimulation.Alphabet m)).nth n = default
      change (ListBlank.mk ([] : List (TapeSimulation.Alphabet m))).nth n = default
      rw [ListBlank.nth_mk,List.getI_nil]

theorem shifted_nth (L : Columns m) (n : ℕ) (i : ℤ) :
    (positionTape m L n).nth i = (bottom m L).nth (i+n) := by
  induction n generalizing i with
  | zero => simp [positionTape]
  | succ n ih =>
      calc
        (positionTape m L (n+1)).nth i = (positionTape m L n).nth (i+1) := by
          simp only [positionTape,Function.iterate_succ_apply',Tape.move_right_nth]
        _ = (bottom m L).nth (i+1+n) := ih (i+1)
        _ = (bottom m L).nth (i+(n+1 : ℕ)) := by congr 1; push_cast; omega

/-- Entire shifted tape, not just its head: every nonblank physical cell has
absolute coordinate in [0,B], with head at the known actual scan position. -/
theorem shifted_blank (L : Columns m) (B : ℕ) (hB : Span m L B) (n : ℕ) (i : ℤ)
    (hi : i+(n : ℤ) < 0 ∨ (B : ℤ) < i+n) : (positionTape m L n).nth i = default := by
  rw [shifted_nth]
  exact bottom_blank m L B hB (i+n) hi

/-- Entire actual tape support relative to its head. The bound applies also
inside bundled move/write/load/test rows, rather than only canonical frames. -/
def Within (R : ℕ) (T : Tape (TapeSimulation.Alphabet m)) : Prop :=
  ∀ i : ℤ, i < -(R : ℤ) ∨ (R : ℤ) < i → T.nth i = default

theorem within_mono (R U : ℕ) (T : Tape (TapeSimulation.Alphabet m))
    (h : Within m R T) (hRU : R ≤ U) : Within m U T := by
  intro i hi
  exact h i (by omega)

theorem within_move (R : ℕ) (T : Tape (TapeSimulation.Alphabet m)) (d : Dir)
    (h : Within m R T) : Within m (R+1) (T.move d) := by
  intro i hi
  cases d
  · rw [Tape.move_left_nth]; exact h (i-1) (by omega)
  · rw [Tape.move_right_nth]; exact h (i+1) (by omega)

theorem within_write (R : ℕ) (T : Tape (TapeSimulation.Alphabet m))
    (symbol : TapeSimulation.Alphabet m) (h : Within m R T) : Within m R (T.write symbol) := by
  intro i hi
  have hn : i ≠ 0 := by omega
  rw [Tape.write_nth,if_neg hn]
  exact h i hi

theorem row_space {L : Type} (q : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) (R : ℕ)
    (h : Within m R T) :
    Within m (R+TapeSimulation.rowOperations m q v T) (TM1.stepAux q v T).Tape := by
  induction q generalizing v T R with
  | move d q ih =>
      simpa [TM1.stepAux,TapeSimulation.rowOperations,Nat.add_assoc] using
        ih v (T.move d) (R+1) (within_move m R T d h)
  | write f q ih =>
      have hw := ih v (T.write (f T.head v)) R (within_write m R T _ h)
      exact within_mono m _ _ _ hw (by simp [TapeSimulation.rowOperations])
  | load f q ih =>
      have hw := ih (f T.head v) T R h
      exact within_mono m _ _ _ hw (by simp [TapeSimulation.rowOperations])
  | branch f q r ihq ihr =>
      cases hf : f T.head v with
      | false =>
          have hw := ihr v T R h
          have hu : Within m (R+(1+TapeSimulation.rowOperations m r v T)) (TM1.stepAux r v T).Tape :=
            within_mono m _ _ _ hw (by omega)
          simpa only [TM1.stepAux,TapeSimulation.rowOperations,hf,Bool.cond_false,Bool.false_eq_true,ite_false]
            using hu
      | true =>
          have hw := ihq v T R h
          have hu : Within m (R+(1+TapeSimulation.rowOperations m q v T)) (TM1.stepAux q v T).Tape :=
            within_mono m _ _ _ hw (by omega)
          simpa only [TM1.stepAux,TapeSimulation.rowOperations,hf,Bool.cond_true,ite_true]
            using hu
  | goto f => exact within_mono m R (R+1) T h (Nat.le_add_right _ 1)
  | halt => exact within_mono m R (R+1) T h (Nat.le_add_right _ 1)

/-- Actual primitive prefixes WITHIN a bundled TM1 row. Branch certificates
are the row's actual test result, not a supplied simulation specification. -/
inductive RowPrefix {L : Type} : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ →
    m.core.σ → Tape (TapeSimulation.Alphabet m) → ℕ → m.core.σ → Tape (TapeSimulation.Alphabet m) → Prop
  | here q v T : RowPrefix q v T 0 v T
  | move d q v T n u U : RowPrefix q v (T.move d) n u U → RowPrefix (.move d q) v T (n+1) u U
  | write f q v T n u U : RowPrefix q v (T.write (f T.head v)) n u U → RowPrefix (.write f q) v T (n+1) u U
  | load f q v T n u U : RowPrefix q (f T.head v) T n u U → RowPrefix (.load f q) v T (n+1) u U
  | branch_true f q r v T n u U : f T.head v = true → RowPrefix q v T n u U →
      RowPrefix (.branch f q r) v T (n+1) u U
  | branch_false f q r v T n u U : f T.head v = false → RowPrefix r v T n u U →
      RowPrefix (.branch f q r) v T (n+1) u U
  | goto f v T : RowPrefix (.goto f) v T 1 v T
  | halt v T : RowPrefix .halt v T 1 v T

theorem row_prefix_cost {L : Type} (q : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) (n : ℕ) (u : m.core.σ)
    (U : Tape (TapeSimulation.Alphabet m)) (hp : RowPrefix m q v T n u U) :
    n ≤ TapeSimulation.rowOperations m q v T := by
  induction hp with
  | here => exact Nat.zero_le _
  | move d q v T n u U hp ih =>
      simpa [TapeSimulation.rowOperations,Nat.add_comm] using Nat.add_le_add_right ih 1
  | write f q v T n u U hp ih =>
      simpa [TapeSimulation.rowOperations,Nat.add_comm] using Nat.add_le_add_right ih 1
  | load f q v T n u U hp ih =>
      simpa [TapeSimulation.rowOperations,Nat.add_comm] using Nat.add_le_add_right ih 1
  | branch_true f q r v T n u U hf hp ih =>
      simpa [TapeSimulation.rowOperations,hf,Nat.add_comm] using Nat.add_le_add_right ih 1
  | branch_false f q r v T n u U hf hp ih =>
      simpa [TapeSimulation.rowOperations,hf,Nat.add_comm] using Nat.add_le_add_right ih 1
  | goto => exact le_rfl
  | halt => exact le_rfl

theorem row_prefix_space {L : Type} (q : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) (n : ℕ) (u : m.core.σ)
    (U : Tape (TapeSimulation.Alphabet m)) (hp : RowPrefix m q v T n u U)
    (R : ℕ) (h : Within m R T) : Within m (R+n) U := by
  induction hp generalizing R with
  | here => simpa using h
  | move d q v T n u U hp ih =>
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (R+1) (within_move m R T d h)
  | write f q v T n u U hp ih =>
      exact within_mono m _ _ _ (ih R (within_write m R T _ h)) (by omega)
  | load f q v T n u U hp ih => exact within_mono m _ _ _ (ih R h) (by omega)
  | branch_true f q r v T n u U hf hp ih => exact within_mono m _ _ _ (ih R h) (by omega)
  | branch_false f q r v T n u U hf hp ih => exact within_mono m _ _ _ (ih R h) (by omega)
  | goto => exact within_mono m R (R+1) _ h (Nat.le_add_right _ 1)
  | halt => exact within_mono m R (R+1) _ h (Nat.le_add_right _ 1)

theorem step_space (token : Option Bool) (a b : FiniteCfg m)
    (hstep : TapeSimulation.finiteStep m token a = some b) (R : ℕ) (h : Within m R a.Tape) :
    Within m (R+TapeSimulation.rowBudget m) b.Tape := by
  cases hl : a.l with
  | none => simp [TapeSimulation.finiteStep,hl] at hstep
  | some l =>
      have chosen (bit : Bool)
          (hb : TM1.stepAux (if bit then (TapeSimulation.programme m).alternate l else
            (TapeSimulation.programme m).core l) a.var a.Tape = b) : Within m (R+TapeSimulation.rowBudget m) b.Tape := by
        have hs := row_space m (if bit then (TapeSimulation.programme m).alternate l else
          (TapeSimulation.programme m).core l) a.var a.Tape R h
        rw [hb] at hs
        exact within_mono m _ _ _ hs (Nat.add_le_add_left (TapeSimulation.row_budget m bit l a.var a.Tape) R)
      cases token with
      | none =>
          cases hc : (TapeSimulation.programme m).choose l
          · exact chosen false (Option.some.inj (by simpa [TapeSimulation.finiteStep,hl,hc] using hstep))
          · simp [TapeSimulation.finiteStep,hl,hc] at hstep
      | some bit =>
          cases hc : (TapeSimulation.programme m).choose l
          · simp [TapeSimulation.finiteStep,hl,hc] at hstep
          · exact chosen bit (Option.some.inj (by simpa [TapeSimulation.finiteStep,hl,hc] using hstep))

theorem instruction_space (instructions : List (Option Bool)) (a b : FiniteCfg m)
    (htrace : TapeSimulation.InstructionTrace m instructions a b) (R : ℕ) (h : Within m R a.Tape) :
    Within m (R+instructions.length*TapeSimulation.rowBudget m) b.Tape := by
  induction instructions generalizing a R with
  | nil => change a = b at htrace; subst b; simpa using h
  | cons token tokens ih =>
      obtain ⟨mid,hs,hr⟩ := htrace
      have hm := step_space m token a mid hs R h
      simpa [List.length_cons,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih mid hr (R+TapeSimulation.rowBudget m) hm

/-- Signed head movement of the actual bundled row. Writes, loads and tests
use the same evolving tape/state as stepAux; only actual move instructions
change the displacement. This is a mathematical resource observer. -/
def dirShift : Dir → ℤ | .left => -1 | .right => 1
def rowShift {L : Type} : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ →
    m.core.σ → Tape (TapeSimulation.Alphabet m) → ℤ
  | .move d q,v,T => dirShift d+rowShift q v (T.move d)
  | .write f q,v,T => rowShift q v (T.write (f T.head v))
  | .load f q,v,T => rowShift q (f T.head v) T
  | .branch f q r,v,T => if f T.head v then rowShift q v T else rowShift r v T
  | .goto _,_,_ => 0
  | .halt,_,_ => 0

theorem row_shift_bound {L : Type} (q : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) :
    -(TapeSimulation.rowOperations m q v T : ℤ) ≤ rowShift m q v T ∧
      rowShift m q v T ≤ (TapeSimulation.rowOperations m q v T : ℤ) := by
  induction q generalizing v T with
  | move d q ih =>
      have h := ih v (T.move d)
      cases d <;> simp only [rowShift,dirShift,TapeSimulation.rowOperations,Nat.cast_add,Nat.cast_one] <;> omega
  | write f q ih =>
      have h := ih v (T.write (f T.head v))
      simp only [rowShift,TapeSimulation.rowOperations,Nat.cast_add,Nat.cast_one]
      omega
  | load f q ih =>
      have h := ih (f T.head v) T
      simp only [rowShift,TapeSimulation.rowOperations,Nat.cast_add,Nat.cast_one]
      omega
  | branch f q r ihq ihr =>
      cases hf : f T.head v with
      | false =>
          have h := ihr v T
          simp only [rowShift,TapeSimulation.rowOperations,hf,Bool.false_eq_true,ite_false,Nat.cast_add,Nat.cast_one]
          omega
      | true =>
          have h := ihq v T
          simp only [rowShift,TapeSimulation.rowOperations,hf,ite_true,Nat.cast_add,Nat.cast_one]
          omega
  | goto => simp [rowShift,TapeSimulation.rowOperations]
  | halt => simp [rowShift,TapeSimulation.rowOperations]

/-- Signed head movement after n actual primitives of this row, with tests,
loads and writes evaluated on their real evolving tape. RowPrefix below is
the receipt that n is a physical pre rather than beyond goto/halt. -/
def primitiveShift {L : Type} : ℕ → TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ →
    m.core.σ → Tape (TapeSimulation.Alphabet m) → ℤ
  | 0,_,_,_ => 0
  | n+1,.move d q,v,T => dirShift d+primitiveShift n q v (T.move d)
  | n+1,.write f q,v,T => primitiveShift n q v (T.write (f T.head v))
  | n+1,.load f q,v,T => primitiveShift n q (f T.head v) T
  | n+1,.branch f q r,v,T => if f T.head v then primitiveShift n q v T else primitiveShift n r v T
  | _+1,.goto _,_,_ => 0
  | _+1,.halt,_,_ => 0

theorem primitive_shift_bound {L : Type} (n : ℕ)
    (q : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) :
    -(n : ℤ) ≤ primitiveShift m n q v T ∧ primitiveShift m n q v T ≤ (n : ℤ) := by
  induction n generalizing q v T with
  | zero => simp [primitiveShift]
  | succ n ih =>
      cases q with
      | move d q =>
          have h := ih q v (T.move d)
          cases d <;> simp only [primitiveShift,dirShift,Nat.cast_add,Nat.cast_one] <;> omega
      | write f q =>
          have h := ih q v (T.write (f T.head v))
          simp only [primitiveShift,Nat.cast_add,Nat.cast_one]
          omega
      | load f q =>
          have h := ih q (f T.head v) T
          simp only [primitiveShift,Nat.cast_add,Nat.cast_one]
          omega
      | branch f q r =>
          cases hf : f T.head v
          · have h := ih r v T
            simp only [primitiveShift,hf,Bool.false_eq_true,ite_false,Nat.cast_add,Nat.cast_one]
            omega
          · have h := ih q v T
            simp only [primitiveShift,hf,ite_true,Nat.cast_add,Nat.cast_one]
            omega
      | goto => simp [primitiveShift]; omega
      | halt => simp [primitiveShift]; omega

theorem bounded_position (R : ℕ) (δ : ℤ) (h : -(R : ℤ) ≤ δ ∧ δ ≤ (R : ℤ)) :
    ∃ i : Fin (2*R+1), (i.val : ℤ)-(R : ℤ) = δ := by
  have hnon : 0 ≤ δ+(R : ℤ) := by omega
  have hcast : ((δ+(R : ℤ)).toNat : ℤ) = δ+(R : ℤ) := Int.toNat_of_nonneg hnon
  have hlt : (δ+(R : ℤ)).toNat < 2*R+1 := by omega
  exact ⟨⟨(δ+(R : ℤ)).toNat,hlt⟩,by dsimp; omega⟩

def transitionShift (token : Option Bool) (a : FiniteCfg m) : ℤ :=
  match a.l,token with
  | none,_ => 0
  | some l,none => if (TapeSimulation.programme m).choose l then 0
      else rowShift m ((TapeSimulation.programme m).core l) a.var a.Tape
  | some l,some bit => if (TapeSimulation.programme m).choose l then
      rowShift m (if bit then (TapeSimulation.programme m).alternate l else
        (TapeSimulation.programme m).core l) a.var a.Tape else 0

theorem transition_shift_bound (token : Option Bool) (a : FiniteCfg m) :
    -(TapeSimulation.rowBudget m : ℤ) ≤ transitionShift m token a ∧
      transitionShift m token a ≤ (TapeSimulation.rowBudget m : ℤ) := by
  have chosen (bit : Bool) (l : TapeSimulation.Label m) :
      -(TapeSimulation.rowBudget m : ℤ) ≤ rowShift m
        (if bit then (TapeSimulation.programme m).alternate l else
          (TapeSimulation.programme m).core l) a.var a.Tape ∧
      rowShift m (if bit then (TapeSimulation.programme m).alternate l else
        (TapeSimulation.programme m).core l) a.var a.Tape ≤ (TapeSimulation.rowBudget m : ℤ) := by
    have h := row_shift_bound m
      (if bit then (TapeSimulation.programme m).alternate l else (TapeSimulation.programme m).core l) a.var a.Tape
    have hb := TapeSimulation.row_budget m bit l a.var a.Tape
    omega
  cases hl : a.l with
  | none => simp [transitionShift,hl]
  | some l =>
      cases token with
      | none =>
          cases hb : (TapeSimulation.programme m).choose l
          · simpa [transitionShift,hl,hb] using chosen false l
          · simp [transitionShift,hl,hb]
      | some bit =>
          cases hb : (TapeSimulation.programme m).choose l
          · simp [transitionShift,hl,hb]
          · simpa [transitionShift,hl,hb] using chosen bit l

def instructionShift : List (Option Bool) → FiniteCfg m → ℤ
  | [],_ => 0
  | token::tokens,a => match TapeSimulation.finiteStep m token a with
      | none => 0
      | some b => transitionShift m token a+instructionShift tokens b

theorem instruction_shift_bound (instructions : List (Option Bool)) (a b : FiniteCfg m)
    (htrace : TapeSimulation.InstructionTrace m instructions a b) :
    -(instructions.length*TapeSimulation.rowBudget m : ℤ) ≤ instructionShift m instructions a ∧
      instructionShift m instructions a ≤ (instructions.length*TapeSimulation.rowBudget m : ℤ) := by
  induction instructions generalizing a with
  | nil => simp [instructionShift]
  | cons token tokens ih =>
      obtain ⟨mid,hs,hr⟩ := htrace
      have ht := transition_shift_bound m token a
      have hm := ih mid hr
      simp only [instructionShift,hs,List.length_cons,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      push_cast at hm
      constructor <;> nlinarith

/-- Compare two actual executions driven by the same available chronological
guess stream. A real halted execution contains every such finite pre;
there is no assumption that the pre itself reaches a boundary or halt. -/
theorem instruction_prefix (pre full : List (Option Bool)) (a b c : FiniteCfg m)
    (hp : TapeSimulation.InstructionTrace m pre a b)
    (hf : TapeSimulation.InstructionTrace m full a c) (hc : c.l = none)
    (left right : List Bool) (hlog : pre.filterMap id++left = full.filterMap id++right) :
    ∃ rest, full = pre++rest ∧ TapeSimulation.InstructionTrace m rest b c := by
  induction pre generalizing full a with
  | nil =>
      change a = b at hp
      subst a
      exact ⟨full,rfl,hf⟩
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := hp
      cases full with
      | nil =>
          change a = c at hf
          subst a
          rw [PathSegmentation.halt_no_edge m c hc token] at hs
          cases hs
      | cons other others =>
          obtain ⟨next',ht,hr'⟩ := hf
          have hlogs : token.toList++(tokens.filterMap id++left) =
              other.toList++(others.filterMap id++right) := by
            cases token <;> cases other <;> exact hlog
          obtain ⟨he,hnext,hrest⟩ := PathSegmentation.edge_log m token other a next next' _ _ hs ht hlogs
          subst other
          subst next'
          obtain ⟨rest,hcut,htrace⟩ := ih others next hr hr' hrest
          exact ⟨rest,by simp only [hcut,List.cons_append],htrace⟩

/-- No dead active control: the installed nonbranch row has its None edge,
and an installed split row has an actual false choice edge. -/
theorem active_edge (a : FiniteCfg m) (h : a.l.isSome = true) :
    ∃ token b, TapeSimulation.finiteStep m token a = some b := by
  cases hl : a.l with
  | none => simp [hl] at h
  | some l =>
      cases hc : (TapeSimulation.programme m).choose l
      · exact ⟨none,TM1.stepAux ((TapeSimulation.programme m).core l) a.var a.Tape,
          by simp [TapeSimulation.finiteStep,hl,hc]⟩
      · exact ⟨some false,TM1.stepAux ((TapeSimulation.programme m).core l) a.var a.Tape,
          by simp [TapeSimulation.finiteStep,hl,hc]⟩

theorem interior_instructions (n : ℕ) (a b : FiniteCfg m)
    (h : PathSegmentation.Interior m n a b) :
    TapeSimulation.InstructionTrace m (List.replicate n none) a b := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
      obtain ⟨next,hs,hr⟩ := h
      exact ⟨next,(TapeSimulation.finite_internal_no_choice m a next hs).1,ih next hr⟩

/-- The installed interior scanner either returns at its first boundary or
uses the entire observed pre without returning. No endpoint law is input. -/
theorem first_boundary_or_end (instructions : List (Option Bool)) (a b : FiniteCfg m)
    (h : TapeSimulation.InstructionTrace m instructions a b) :
    (∃ n rest mid, instructions = List.replicate n none++rest ∧
      PathSegmentation.Interior m n a mid ∧ PathSegmentation.atBoundary m mid ∧
      TapeSimulation.InstructionTrace m rest mid b ∧ rest.length ≤ instructions.length) ∨
    (instructions = List.replicate instructions.length none ∧
      PathSegmentation.Interior m instructions.length a b ∧ ¬ PathSegmentation.atBoundary m b) := by
  induction instructions generalizing a with
  | nil =>
      change a = b at h
      subst a
      by_cases hb : PathSegmentation.atBoundary m b
      · exact Or.inl ⟨0,[],b,rfl,rfl,hb,rfl,le_rfl⟩
      · exact Or.inr ⟨rfl,rfl,hb⟩
  | cons token tokens ih =>
      by_cases ha : PathSegmentation.atBoundary m a
      · exact Or.inl ⟨0,token::tokens,a,rfl,rfl,ha,h,le_rfl⟩
      · obtain ⟨next,hs,hr⟩ := h
        obtain ⟨ht,hi,hn⟩ := PathSegmentation.internal_edge m token a next ha hs
        subst token
        rcases ih next hr with ⟨n,rest,mid,hcut,hint,hmid,hrest,hlen⟩ | ⟨hword,hint,hend⟩
        · refine Or.inl ⟨n+1,rest,mid,?_,⟨next,hi,hint⟩,hmid,hrest,?_⟩
          · simp only [List.replicate_succ,List.cons_append,hcut]
          · exact hlen.trans (by simp)
        · refine Or.inr ⟨?_,?_,hend⟩
          · simpa only [List.length_cons,List.replicate_succ] using congrArg (none :: ·) hword
          · exact ⟨next,hi,hint⟩

/-- Zero unfinished rows, or precisely one started source statement followed
by actual deterministic internal rows, ending strictly before its boundary. -/
def Pending (instructions : List (Option Bool)) (a b : FiniteCfg m) : Prop :=
  (instructions = [] ∧ a = b) ∨ ∃ token first n,
    instructions = token::List.replicate n none ∧ TapeSimulation.finiteStep m token a = some first ∧
    PathSegmentation.Interior m n first b ∧ ¬ PathSegmentation.atBoundary m b

/-- Reverse segmentation for an arbitrary unfinished actual microtrajectory.
The complete rows and at most one unfinished interval are produced internally. -/
theorem prefix_segmentation (instructions : List (Option Bool)) (a b : FiniteCfg m)
    (ha : PathSegmentation.atBoundary m a)
    (h : TapeSimulation.InstructionTrace m instructions a b) :
    ∃ done pending tokens mid, instructions = done++pending ∧
      TapeSimulation.InstructionTrace m done a mid ∧ PathSegmentation.RealTrace m tokens a mid ∧
      Pending m pending mid b ∧ done.filterMap id = tokens.filterMap id := by
  induction hlen : instructions.length using Nat.strong_induction_on generalizing instructions a with
  | h length ih =>
      cases instructions with
      | nil =>
          change a = b at h
          subst a
          exact ⟨[],[],[],b,rfl,rfl,rfl,Or.inl ⟨rfl,rfl⟩,rfl⟩
      | cons token instructions =>
          obtain ⟨first,hfirst,hrest⟩ := h
          rcases first_boundary_or_end m instructions first b hrest with
            ⟨n,rest,returnCfg,hcut,hint,hreturn,hr,hrlen⟩ | ⟨hword,hint,hend⟩
          · have hlt : rest.length < length := by simp only [List.length_cons] at hlen; omega
            obtain ⟨done,pending,tokens,mid,hcut',hdone,hreal,hpending,hlog⟩ :=
              ih rest.length hlt (instructions := rest) (a := returnCfg) hreturn hr rfl
            have hround : TapeSimulation.InstructionTrace m (token::List.replicate n none) a returnCfg :=
              ⟨first,hfirst,interior_instructions m n first returnCfg hint⟩
            refine ⟨(token::List.replicate n none)++done,pending,token::tokens,mid,?_,
              TapeSimulation.instruction_append m _ _ a returnCfg mid hround hdone,
              ⟨returnCfg,⟨first,hfirst,PathSegmentation.interior_reaches m n first returnCfg hint,hreturn⟩,hreal⟩,
              hpending,?_⟩
            · simp only [hcut,hcut',List.cons_append,List.append_assoc]
            · rw [List.filterMap_append,hlog]
              cases token <;> simp
          · exact ⟨[],token::instructions,[],a,rfl,rfl,rfl,
              Or.inr ⟨token,first,instructions.length,congrArg (token :: ·) hword,hfirst,hint,hend⟩,rfl⟩

/-! Fixed finite symbol codes used ONLY to measure faithful configurations.
These are representation metadata; no encode/decode callback is installed. -/
namespace CellBits
variable {A : Type} [Fintype A]
def width (A : Type) [Fintype A] : ℕ := Fintype.card A+1
def bit (a : A) (i : Fin (width A)) : Bool :=
  decide ((Fintype.equivFin A a).val = i.val)
def code (a : A) : List Bool := List.ofFn (bit a)
def word (xs : List A) : List Bool := xs.flatMap code
@[simp] theorem width_pos : 0 < width A := by simp [width]
@[simp] theorem code_length (a : A) : (code a).length = width A := List.length_ofFn
theorem code_injective : Function.Injective (code : A → List Bool) := by
  intro a b h
  have hf : bit a = bit b := List.ofFn_injective h
  let i : Fin (width A) := ⟨(Fintype.equivFin A a).val,by
    have ha := (Fintype.equivFin A a).isLt
    simp only [width]
    omega⟩
  have hb : (Fintype.equivFin A b).val = (Fintype.equivFin A a).val := by
    have hi := congrFun hf i
    simpa [bit,i] using hi.symm
  exact (Fintype.equivFin A).injective (Fin.ext hb.symm)
@[simp] theorem word_length (xs : List A) : (word xs).length = width A*xs.length := by
  induction xs with
  | nil => simp [word]
  | cons a xs ih => simp [word,List.flatMap_cons,code_length,ih,Nat.mul_succ,Nat.add_comm,Nat.mul_comm]
theorem word_injective : Function.Injective (word : List A → List Bool) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      have hl := congrArg List.length h
      simp only [word_length,List.length_nil,Nat.mul_zero] at hl
      have hz : ys.length = 0 := by
        rcases Nat.mul_eq_zero.mp hl.symm with hw | hy
        · exact False.elim ((Nat.ne_of_gt (width_pos (A := A))) hw)
        · exact hy
      exact (List.length_eq_zero_iff.mp hz).symm
  | cons a xs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hl := congrArg List.length h
          simp only [word_length,List.length_cons,List.length_nil,Nat.mul_zero] at hl
          exact False.elim ((Nat.ne_of_gt (Nat.mul_pos (width_pos (A := A)) (Nat.succ_pos xs.length))) hl)
      | cons b ys =>
          have hp := congrArg (List.take (width A)) h
          have hc : code a = code b := by
            simpa [word,List.flatMap_cons,List.take_append,code_length] using hp
          have hab : a = b := code_injective hc
          subst b
          have hr : word xs = word ys :=
            List.append_cancel_left (by simpa only [word,List.flatMap_cons] using h)
          exact congrArg (a :: ·) (ih hr)
end CellBits

def window (R : ℕ) (T : Tape (TapeSimulation.Alphabet m)) : Fin (2*R+1) → TapeSimulation.Alphabet m :=
  fun i => T.nth ((i.val : ℤ)-R)

/-- Every cell outside the captured finite window is physically blank.
Consequently equal captured cells determine the entire quotient tape. -/
theorem window_faithful (R : ℕ) (T U : Tape (TapeSimulation.Alphabet m))
    (hT : Within m R T) (hU : Within m R U) (hw : window m R T = window m R U) : T = U := by
  have hn : ∀ i : ℤ, T.nth i = U.nth i := by
    intro i
    by_cases hi : -(R : ℤ) ≤ i ∧ i ≤ (R : ℤ)
    · have hnon : 0 ≤ i+(R : ℤ) := by omega
      have hcast : ((i+(R : ℤ)).toNat : ℤ) = i+(R : ℤ) := Int.toNat_of_nonneg hnon
      have hlt : (i+(R : ℤ)).toNat < 2*R+1 := by omega
      let j : Fin (2*R+1) := ⟨(i+(R : ℤ)).toNat,hlt⟩
      have hc := congrFun hw j
      have hj : (j.val : ℤ)-(R : ℤ) = i := by dsimp [j]; omega
      simpa only [window,hj] using hc
    · rw [hT i (by omega),hU i (by omega)]
  have hh : T.head = U.head := hn 0
  have hl : T.left = U.left := ListBlank.ext (fun n => hn (Int.negSucc n))
  have hr : T.right = U.right := ListBlank.ext (fun n => hn ((n+1 : ℕ) : ℤ))
  cases T
  cases U
  cases hh
  cases hl
  cases hr
  rfl

def windowBits (R : ℕ) (T : Tape (TapeSimulation.Alphabet m)) : Fin (2*R+1) → List Bool :=
  fun i => CellBits.code (window m R T i)

theorem window_bits_faithful (R : ℕ) (T U : Tape (TapeSimulation.Alphabet m))
    (hT : Within m R T) (hU : Within m R U) (h : windowBits m R T = windowBits m R U) : T = U := by
  apply window_faithful m R T U hT hU
  funext i
  exact CellBits.code_injective (congrFun h i)

local instance : Fintype m.core.σ := m.core.σFin
def controlWidth : ℕ := CellBits.width (Option (TapeSimulation.Label m))+CellBits.width m.core.σ
def symbolWidth : ℕ := CellBits.width (TapeSimulation.Alphabet m)

/-- Literal fixed-width snapshot of the actual finite control, register state
and every tape cell in the proved window. The window's position/size is fixed
by the resource theorem, not decoded by the runtime machine. -/
def snapshot (R : ℕ) (c : FiniteCfg m) : List Bool :=
  CellBits.code c.l++CellBits.code c.var++CellBits.word (List.ofFn (window m R c.Tape))

theorem snapshot_length (R : ℕ) (c : FiniteCfg m) :
    (snapshot m R c).length = controlWidth m+symbolWidth m*(2*R+1) := by
  simp [snapshot,controlWidth,symbolWidth,CellBits.word_length,CellBits.code_length,Nat.add_assoc]

theorem snapshot_cells_faithful (R : ℕ) (c d : FiniteCfg m)
    (hc : Within m R c.Tape) (hd : Within m R d.Tape)
    (hlabel : CellBits.code c.l = CellBits.code d.l)
    (hstate : CellBits.code c.var = CellBits.code d.var)
    (htape : windowBits m R c.Tape = windowBits m R d.Tape) : c = d := by
  have hl := CellBits.code_injective hlabel
  have hs := CellBits.code_injective hstate
  have ht := window_bits_faithful m R c.Tape d.Tape hc hd htape
  cases c
  cases d
  cases hl
  cases hs
  cases ht
  rfl

theorem snapshot_faithful (R : ℕ) (c d : FiniteCfg m)
    (hc : Within m R c.Tape) (hd : Within m R d.Tape)
    (h : snapshot m R c = snapshot m R d) : c = d := by
  have hp := congrArg (List.take (CellBits.width (Option (TapeSimulation.Label m)))) h
  have hl : CellBits.code c.l = CellBits.code d.l := by
    simpa [snapshot,List.take_append,CellBits.code_length] using hp
  have hrest : CellBits.code c.var++CellBits.word (List.ofFn (window m R c.Tape)) =
      CellBits.code d.var++CellBits.word (List.ofFn (window m R d.Tape)) := by
    have he : CellBits.code d.l++(CellBits.code c.var++CellBits.word (List.ofFn (window m R c.Tape))) =
        CellBits.code d.l++(CellBits.code d.var++CellBits.word (List.ofFn (window m R d.Tape))) := by
      simpa only [snapshot,List.append_assoc,hl] using h
    exact List.append_cancel_left he
  have hs : CellBits.code c.var = CellBits.code d.var := by
    have hv := congrArg (List.take (CellBits.width m.core.σ)) hrest
    simpa [List.take_append,CellBits.code_length] using hv
  have ht : CellBits.word (List.ofFn (window m R c.Tape)) =
      CellBits.word (List.ofFn (window m R d.Tape)) :=
    List.append_cancel_left (by simpa only [hs] using hrest)
  have hw := List.ofFn_injective (CellBits.word_injective ht)
  apply snapshot_cells_faithful m R c d hc hd hl hs
  funext i
  exact congrArg CellBits.code (congrFun hw i)

/-! The residual opcode is itself finite: exactly the old Mathlib subterm
closures of the SAME two installed tables, including the row-done marker. -/
open scoped Classical in
def primitiveControls : Finset (Option (TM1.Stmt (TapeSimulation.Alphabet m) (TapeSimulation.Label m) m.core.σ)) :=
  TM1.stmts (TapeSimulation.programme m).core Finset.univ ∪
    TM1.stmts (TapeSimulation.programme m).alternate Finset.univ
abbrev PrimitiveControl := {q // q ∈ primitiveControls m}
noncomputable instance : Fintype (PrimitiveControl m) := by classical exact inferInstance

def residual {L : Type} : ℕ → TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ →
    m.core.σ → Tape (TapeSimulation.Alphabet m) → Option (TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ)
  | 0,q,_,_ => some q
  | n+1,.move d q,v,T => residual n q v (T.move d)
  | n+1,.write f q,v,T => residual n q v (T.write (f T.head v))
  | n+1,.load f q,v,T => residual n q (f T.head v) T
  | n+1,.branch f q r,v,T => if f T.head v then residual n q v T else residual n r v T
  | _+1,.goto _,_,_ => none
  | _+1,.halt,_,_ => none

theorem residual_subterm {L : Type} (n : ℕ) (q : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) (r : TM1.Stmt (TapeSimulation.Alphabet m) L m.core.σ)
    (h : residual m n q v T = some r) : r ∈ TM1.stmts₁ q := by
  classical
  induction n generalizing q v T with
  | zero =>
      have he : q = r := Option.some.inj h
      subst r
      exact TM1.stmts₁_self
  | succ n ih =>
      cases q with
      | move d q => exact Finset.mem_insert_of_mem (ih q v (T.move d) h)
      | write f q => exact Finset.mem_insert_of_mem (ih q v (T.write (f T.head v)) h)
      | load f q => exact Finset.mem_insert_of_mem (ih q (f T.head v) T h)
      | branch f q s =>
          cases hf : f T.head v
          · have hr := ih s v T (by simpa [residual,hf] using h)
            exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hr)
          · have hr := ih q v T (by simpa [residual,hf] using h)
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hr)
      | goto => cases h
      | halt => cases h

theorem residual_control_mem (bit : Bool) (l : TapeSimulation.Label m) (n : ℕ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) :
    residual m n (if bit then (TapeSimulation.programme m).alternate l else (TapeSimulation.programme m).core l) v T ∈
      primitiveControls m := by
  classical
  have installed (p : TapeSimulation.Label m → TM1.Stmt (TapeSimulation.Alphabet m) (TapeSimulation.Label m) m.core.σ) :
      residual m n (p l) v T ∈ TM1.stmts p Finset.univ := by
    cases hr : residual m n (p l) v T with
    | none => simp [TM1.stmts,Finset.mem_insertNone]
    | some r =>
        apply TM1.stmts_trans (residual_subterm m n (p l) v T r hr)
        simp only [TM1.stmts,Finset.mem_insertNone,Option.mem_def,Option.some.injEq,forall_eq',Finset.mem_biUnion]
        exact ⟨l,Finset.mem_univ l,TM1.stmts₁_self⟩
  cases bit
  · exact Finset.mem_union_left _ (installed (TapeSimulation.programme m).core)
  · exact Finset.mem_union_right _ (installed (TapeSimulation.programme m).alternate)

def residualControl (bit : Bool) (l : TapeSimulation.Label m) (n : ℕ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) : PrimitiveControl m :=
  ⟨_,residual_control_mem m bit l n v T⟩

def primitiveSnapshot (R : ℕ) (bit : Bool) (l : TapeSimulation.Label m) (n : ℕ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) (c : FiniteCfg m) : List Bool :=
  CellBits.code (residualControl m bit l n v T)++snapshot m R c

theorem primitive_snapshot_length (R : ℕ) (bit : Bool) (l : TapeSimulation.Label m) (n : ℕ)
    (v : m.core.σ) (T : Tape (TapeSimulation.Alphabet m)) (c : FiniteCfg m) :
    (primitiveSnapshot m R bit l n v T c).length = CellBits.width (PrimitiveControl m)+
      (controlWidth m+symbolWidth m*(2*R+1)) := by
  rw [primitiveSnapshot,List.length_append,CellBits.code_length,snapshot_length]

theorem primitive_snapshot_faithful (R : ℕ) (bit bit' : Bool) (l l' : TapeSimulation.Label m)
    (n n' : ℕ) (v v' : m.core.σ) (T T' : Tape (TapeSimulation.Alphabet m)) (c d : FiniteCfg m)
    (hc : Within m R c.Tape) (hd : Within m R d.Tape)
    (h : primitiveSnapshot m R bit l n v T c = primitiveSnapshot m R bit' l' n' v' T' d) :
    residualControl m bit l n v T = residualControl m bit' l' n' v' T' ∧ c = d := by
  have hp := congrArg (List.take (CellBits.width (PrimitiveControl m))) h
  have hcode : CellBits.code (residualControl m bit l n v T) =
      CellBits.code (residualControl m bit' l' n' v' T') := by
    simpa [primitiveSnapshot,List.take_append,CellBits.code_length] using hp
  have hs : snapshot m R c = snapshot m R d :=
    List.append_cancel_left (by simpa only [primitiveSnapshot,hcode] using h)
  exact ⟨CellBits.code_injective hcode,snapshot_faithful m R c d hc hd hs⟩

theorem scan_prefix_space (k : m.core.K) (v : m.core.σ) (S : ∀ k, List (m.core.Γ k))
    (L : Columns m) (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (B : ℕ) (hB : ∀ k, (S k).length ≤ B) (n : ℕ) (hn : n ≤ (S k).length) :
    n ≤ B ∧ (positionTape m L n).head.1 = decide (n = 0) ∧
      ∀ i : ℤ, i+n < 0 ∨ (B : ℤ) < i+n → (positionTape m L n).nth i = default :=
  ⟨hn.trans (hB k),head_marker m L n,fun i hi => shifted_blank m L B (columns_span m v S L hL B hB) n i hi⟩

/-- The actual action producer gives a new canonical column frame. Both
scans and all action-end states therefore use B+1 as a common space window. -/
theorem round_space (k : m.core.K) (o : TM2to1.StAct m.core.K m.core.Γ m.core.σ k)
    (q : m.core.Stmt) (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) (L : Columns m)
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (B : ℕ) (hB : ∀ k, (S k).length ≤ B) :
    ∃ L' : Columns m,
      Rows m ((S k).length+1+(TM2to1.stWrite v (S k) o).length)
        (go m k o q v L 0) (ret m q (TM2to1.stVar v (S k) o) L' 0) ∧
      Span m L B ∧ Span m L' (B+1) ∧
      (∀ n ≤ (S k).length, n ≤ B ∧ (positionTape m L n).head.1 = decide (n = 0)) ∧
      (∀ n ≤ (TM2to1.stWrite v (S k) o).length,
        n ≤ B+1 ∧ (positionTape m L' n).head.1 = decide (n = 0)) := by
  obtain ⟨L',hL',hr⟩ := action_round m k o q v S L hL
  have hnew := action_capacity m k o v S B hB
  refine ⟨L',hr,columns_span m v S L hL B hB,
    columns_span m (TM2to1.stVar v (S k) o) (actionStacks m k o v S) L' hL' (B+1) hnew,
    ?_,?_⟩
  · intro n hn; exact ⟨hn.trans (hB k),head_marker m L n⟩
  · intro n hn
    exact ⟨hn.trans ((action_length m k o v S).trans (Nat.add_le_add_right (hB k) 1)),head_marker m L' n⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.TapeMicrostepBudget
