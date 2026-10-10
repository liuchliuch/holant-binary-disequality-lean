import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.Code

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Actual fixed-width Boolean pushes and a statically
unrolled pop/branch tree. Prefix words below exist only during construction;
runtime state contains one Option Bool and one validity flag, never a List.
EOF is allowed only before the first bit; partial and invalid blocks reject. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Block
open Turing Computability Holant.Complexity
variable (m : BinaryMachine)
abbrev State := m.core.σ × Option Bool × Bool
def clear (v : m.core.σ) : State m := (v,none,true)
def setBit (v : State m) (b : Option Bool) : State m := (v.1,b,v.2.2)
def bad : TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m) :=
  .load (fun v => (v.1,none,false)) .halt

def pushVector (k : m.core.K) : (n : ℕ) →
    (Fin n → State m → Bool) →
    TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m) →
    TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m)
  | 0,_,next => next
  | n+1,bits,next => .push k (bits (Fin.last n))
      (pushVector k n (fun i => bits i.castSucc) next)

def read (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m)) :
    ℕ → List Bool → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m)
  | 0,pref => (Code.decode m k pref).elim (bad m)
      (fun a => .load (fun v => clear m v.1) (leaf (some a)))
  | n+1,pref => .pop k (setBit m)
      (.branch (fun v => v.2.1.isSome)
        (.branch (fun v => v.2.1.getD false)
          (read k leaf n (pref++[true])) (read k leaf n (pref++[false])))
        (if pref = [] then .load (fun v => clear m v.1) (leaf none) else bad m))

def readSymbol (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m)) :=
  read m k leaf (Code.width m k) []

theorem pushVector_eval (k : m.core.K) (n : ℕ) (bits : Fin n → State m → Bool)
    (next : TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m))
    (v : State m) (S : m.core.K → List Bool) :
    TM2.stepAux (pushVector m k n bits next) v S =
      TM2.stepAux next v (Function.update S k (List.ofFn (fun i => bits i v)++S k)) := by
  induction n generalizing next S with
  | zero => simp [pushVector]
  | succ n ih =>
    rw [pushVector,TM2.stepAux,ih]
    simp only [Function.update_self,Function.update_idem]
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append,List.append_assoc,List.singleton_append]

theorem read_exact (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m))
    (n : ℕ) (pref bits : List Bool) (hlen : bits.length = n) (a : m.core.Γ k)
    (hdecode : Code.decode m k (pref++bits) = some a)
    (v : State m) (S : m.core.K → List Bool) :
    TM2.stepAux (read m k leaf n pref) v (Function.update S k (bits++S k)) =
      TM2.stepAux (leaf (some a)) (clear m v.1) S := by
  induction n generalizing pref bits v S with
  | zero =>
    have hb : bits = [] := List.length_eq_zero_iff.mp hlen
    subst bits
    simp only [List.append_nil] at hdecode
    simp only [read,hdecode,Option.elim_some,TM2.stepAux,
      List.nil_append,Function.update_eq_self]
  | succ n ih =>
    cases bits with
    | nil => simp at hlen
    | cons bit bits =>
      have hn : bits.length = n := by simpa only [List.length_cons,Nat.succ.injEq] using hlen
      cases bit with
      | false =>
        have hd : Code.decode m k ((pref++[false])++bits) = some a := by
          simpa only [List.append_assoc,List.singleton_append] using hdecode
        simpa [read,TM2.stepAux,setBit,List.append_assoc,Function.update_idem] using
          ih (pref++[false]) bits hn hd (setBit m v (some false)) S
      | true =>
        have hd : Code.decode m k ((pref++[true])++bits) = some a := by
          simpa only [List.append_assoc,List.singleton_append] using hdecode
        simpa [read,TM2.stepAux,setBit,List.append_assoc,Function.update_idem] using
          ih (pref++[true]) bits hn hd (setBit m v (some true)) S

theorem read_symbol (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m))
    (a : m.core.Γ k) (v : State m) (S : m.core.K → List Bool) :
    TM2.stepAux (readSymbol m k leaf) v
      (Function.update S k (Code.symbol m k a++S k)) =
        TM2.stepAux (leaf (some a)) (clear m v.1) S := by
  exact read_exact m k leaf _ [] _ (Code.symbol_length m k a) a
    (by simpa only [List.nil_append] using Code.decode_symbol m k a) v S

theorem read_empty (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m))
    (v : State m) (S : m.core.K → List Bool) (hs : S k = []) :
    TM2.stepAux (readSymbol m k leaf) v S = TM2.stepAux (leaf none) (clear m v.1) S := by
  have hu : Function.update S k [] = S := by
    simpa only [hs] using Function.update_eq_self k S
  simp [readSymbol,Code.width,read,TM2.stepAux,setBit,hs,hu]

theorem read_word (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m))
    (v : State m) (S : ∀ j, List (m.core.Γ j)) :
    TM2.stepAux (readSymbol m k leaf) v (Code.tapes m S) =
      TM2.stepAux (leaf (S k).head?) (clear m v.1)
        (Code.tapes m (Function.update S k (S k).tail)) := by
  cases hs : S k with
  | nil =>
    have hc : Code.tapes m S k = [] := by simp [Code.tapes,Code.word,hs]
    have hu : Function.update S k [] = S := by simpa only [hs] using Function.update_eq_self k S
    simpa only [hs,List.head?_nil,List.tail_nil,hu] using read_empty m k leaf v (Code.tapes m S) hc
  | cons a rest =>
    let U := Function.update S k rest
    have hU : U k = rest := by simp [U]
    have ht : Code.tapes m S = Function.update (Code.tapes m U) k
        (Code.symbol m k a++Code.tapes m U k) := by
      rw [Code.tapes_cons]
      congr 1
      funext j
      by_cases hj : j = k
      · subst j; simp [U,hs]
      · simp [U,hj]
    rw [ht,read_symbol]
    simp only [hs,List.head?_cons,List.tail_cons]
    rfl

def peekSymbol (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m)) :=
  readSymbol m k (fun head => head.elim (leaf none) (fun a =>
    pushVector m k (Code.width m k) (fun i _ => Code.bit m k a i) (leaf (some a))))

theorem peek_word (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m))
    (v : State m) (S : ∀ j, List (m.core.Γ j)) :
    TM2.stepAux (peekSymbol m k leaf) v (Code.tapes m S) =
      TM2.stepAux (leaf (S k).head?) (clear m v.1) (Code.tapes m S) := by
  rw [peekSymbol,read_word]
  cases hs : S k with
  | nil =>
    have hu : Function.update S k [] = S := by simpa only [hs] using Function.update_eq_self k S
    simp only [hs,List.head?_nil,List.tail_nil,Option.elim_none,hu]
  | cons a rest =>
    simp only [hs,List.head?_cons,List.tail_cons,Option.elim_some]
    rw [pushVector_eval]
    change TM2.stepAux (leaf (some a)) (clear m v.1)
      (Function.update (Code.tapes m (Function.update S k rest)) k
        (Code.symbol m k a++Code.tapes m (Function.update S k rest) k)) = _
    rw [Code.tapes_cons,Function.update_self,Function.update_idem]
    have hu : Function.update S k (a::rest) = S := by
      simpa only [hs] using Function.update_eq_self k S
    rw [hu]

theorem pushVector_budget (k : m.core.K) (n : ℕ) (bits : Fin n → State m → Bool)
    (next : TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m)) :
    HeterogeneousCost.budget (pushVector m k n bits next) = n+HeterogeneousCost.budget next := by
  induction n generalizing next with
  | zero => simp [pushVector]
  | succ n ih => simp [pushVector,HeterogeneousCost.budget,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem read_budget (k : m.core.K)
    (leaf : Option (m.core.Γ k) → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m))
    (C : ℕ) (hC : ∀ head, HeterogeneousCost.budget (leaf head) ≤ C)
    (n : ℕ) (pref : List Bool) :
    HeterogeneousCost.budget (read m k leaf n pref) ≤ 3*n+C+3 := by
  induction n generalizing pref with
  | zero =>
    cases hd : Code.decode m k pref with
    | none => simp [read,hd,bad,HeterogeneousCost.budget]
    | some a =>
      have hb := hC (some a)
      simp only [read,hd,Option.elim_some,HeterogeneousCost.budget]
      omega
  | succ n ih =>
    have ht := ih (pref++[true])
    have hf := ih (pref++[false])
    have he := hC none
    by_cases hp : pref = []
    · subst pref
      simp only [List.nil_append] at ht hf
      simp only [read,if_pos rfl,ite_true,HeterogeneousCost.budget,List.nil_append]
      omega
    · simp only [read,if_neg hp,bad,HeterogeneousCost.budget]
      omega

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Block
