import Holant.Proofs.Traversal.ArityTwo.OccurrenceWeights
import Holant.Proofs.Traversal.ArityTwo.PortEnumeration
import Holant.Proofs.Traversal.ArityTwo.AssignmentSums


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo
open Holant Holant.Complexity PortWalk Descriptors
open scoped BigOperators
variable {K : Type} [CommSemiring K]

def rightValue (right : Bool → K) : List (Kernel K) → List Bool → K
  | [], [a] => right a
  | M::ms, a::b::bits => M a b * rightValue right ms (b::bits)
  | _, _ => 0

theorem sum_rightValue (ms : List (Kernel K)) (right : Bool → K) (a : Bool) :
    (∑ x : Fin ms.length → Bool, rightValue right ms (a::List.ofFn x)) = message ms right a := by
  induction ms generalizing a with
  | nil => simp [rightValue]
  | cons M ms ih =>
    change (∑ x : Fin (ms.length+1) → Bool, rightValue right (M::ms) (a::List.ofFn x)) = _
    rw [sum_bool_tuples_succ]
    simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,rightValue,← Finset.mul_sum,ih]
    rw [message_cons]
    rfl

theorem sum_path_rightValue (ms : List (Kernel K)) (left right : Bool → K) :
    (∑ x : Fin (ms.length+1) → Bool,
      left (x 0) * rightValue right ms (List.ofFn x)) = pathValue left ms right := by
  rw [sum_bool_tuples_succ]
  simp only [Fin.cons_zero,List.ofFn_succ,Fin.cons_succ,← Finset.mul_sum,sum_rightValue,pathValue]

theorem sum_between_rightValue (n : ℕ) (A : Fin (n+1) → Kernel K) (a b : Bool) :
    (∑ x : Fin n → Bool,
      rightValue (fun _ => 1) (List.ofFn A) (a::List.ofFn x++[b])) = product (List.ofFn A) a b := by
  induction n generalizing a b with
  | zero => simp [List.ofFn_succ,rightValue,product]
  | succ n ih =>
    rw [sum_bool_tuples_succ]
    rw [List.ofFn_succ (f := A)]
    simp only [List.ofFn_cons, Fin.cons_zero, List.cons_append, rightValue]
    change (∑ c : Bool, ∑ x : Fin n → Bool, A 0 a c *
      rightValue (fun _ => 1) (List.ofFn (fun i => A i.succ)) (c :: List.ofFn x ++ [b])) = _
    simp only [← Finset.mul_sum, ih]
    rfl

theorem sum_cycle_rightValue (n : ℕ) (A : Fin (n+1) → Kernel K) :
    (∑ x : Fin (n+1) → Bool,
      rightValue (fun _ => 1) (List.ofFn A) (List.ofFn x++[x 0])) = cycleValue (List.ofFn A) := by
  rw [sum_bool_tuples_succ]
  simp only [List.ofFn_cons, Fin.cons_zero, List.cons_append]
  change (∑ a : Bool, ∑ x : Fin n → Bool,
    rightValue (fun _ => 1) (List.ofFn A) (a :: List.ofFn x ++ [a])) = _
  simp only [sum_between_rightValue, cycleValue, Kernel.trace]

variable {s b : ℕ} {arity : ℕ → ℕ} {A : Type}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (vertex : ∀ v : Fin r.vertices.length, (Fin (degree (arity := arity) r v) → Bool) → A)
variable (edge : Fin r.edges.length → Kernel A) (coeff : A → K)

def vertexWeight (z : r.Ports arity → Bool) (p : r.Ports arity) : K :=
  coeff (vertex p.1 (fun j => z ⟨p.1,j⟩))

def edgeWeight (z : r.Ports arity → Bool) (p : r.Ports arity) : K :=
  coeff (edge (r.route h p).1 (z (r.lookup h ((r.route h p).1,false)))
    (z (r.lookup h ((r.route h p).1,true))))

def walkWeight (z : r.Ports arity → Bool) (xs : List (r.Ports arity)) : K :=
  (xs.map (vertexWeight r vertex coeff z)).prod *
    ((departures r xs).map (edgeWeight r h edge coeff z)).prod

theorem terminal_word_head {p q : r.Ports arity} {xs : List (r.Ports arity)}
    (ht : Trace r h p xs (.terminal q)) : ∃ tail, portWord r xs = p::tail := by
  cases ht with
  | terminal p ho => exact ⟨[],by simp [portWord,ho]⟩
  | step p out xs stop ho ht => exact ⟨_,rfl⟩

theorem repeated_word_head {p q : r.Ports arity} {xs : List (r.Ports arity)}
    (ht : Trace r h p xs (.repeated q)) : ∃ tail, portWord r xs++[q] = p::tail := by
  cases ht with
  | repeated p => exact ⟨[],rfl⟩
  | step p out xs stop ho ht => exact ⟨_,rfl⟩

theorem pathMatrices_weight (hd : ∀ v, degree (arity := arity) r v ≤ 2) (z : r.Ports arity → Bool)
    {p q : r.Ports arity} {xs : List (r.Ports arity)} (ht : Trace r h p xs (.terminal q)) :
    ∀ ms right, pathMatrices r h vertex edge xs = some (ms,right) →
      rightValue (fun b => coeff (right b)) (ms.map (realizeMatrix coeff)) ((portWord r xs).map z) =
        walkWeight r h vertex edge coeff z xs := by
  generalize hs : Stop.terminal q = stop at ht
  induction ht with
  | repeated p => cases hs
  | terminal p ho =>
    intro ms right hm
    have hp := terminal_unary r hd p ho
    simp only [pathMatrices,hp,if_pos, List.isEmpty_nil,Option.some.injEq,Prod.mk.injEq] at hm
    obtain ⟨rfl,rfl⟩ := hm
    simpa [portWord,ho,rightValue,walkWeight,departures,vertexWeight] using
      unaryTable_at_assignment r vertex coeff z p hp
  | step p out xs stop ho ht ih =>
    subst stop
    intro ms right hm
    obtain ⟨tail,cap,hcap⟩ := pathMatrices_trace r h vertex edge hd ht
    have hp : degree (arity := arity) r p.1 ≠ 1 := by have hd := (other_some r p out ho).2.2; omega
    simp only [pathMatrices,if_neg hp,ho,hcap,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at hm
    obtain ⟨rfl,rfl⟩ := hm
    obtain ⟨bits,hbits⟩ := terminal_word_head r h ht
    have hi := ih rfl tail cap hcap
    rw [hbits] at hi
    simp only [List.map_cons] at hi
    simp only [portWord,ho,Option.toList_some,List.cons_append,List.nil_append,List.map_cons,
      hbits,rightValue]
    rw [binaryTable_at_assignment r vertex coeff z p out ho,
      edgeTable_at_assignment r h edge coeff z out,hi]
    simp only [walkWeight,departures,ho,Option.toList_some,List.cons_append,List.nil_append,
      List.map_cons,List.prod_cons,List.filterMap_cons,ho,vertexWeight,edgeWeight]
    ac_rfl

theorem cycleMatrices_weight (z : r.Ports arity → Bool)
    {p q : r.Ports arity} {xs : List (r.Ports arity)} (ht : Trace r h p xs (.repeated q)) :
    ∀ ms, cycleMatrices r h vertex edge xs = some ms →
      rightValue (fun _ => 1) (ms.map (realizeMatrix coeff)) ((portWord r xs).map z++[z q]) =
        walkWeight r h vertex edge coeff z xs := by
  generalize hs : Stop.repeated q = stop at ht
  induction ht with
  | terminal p ho => cases hs
  | repeated p =>
    cases hs
    intro ms hm
    have hm' : ms = [] := by simpa [cycleMatrices] using hm.symm
    subst ms
    simp [rightValue,portWord,walkWeight,departures]
  | step p out xs stop ho ht ih =>
    subst stop
    intro ms hm
    obtain ⟨tail,hcap⟩ := cycleMatrices_trace r h vertex edge ht
    simp only [cycleMatrices,ho,hcap,Option.bind_some,bind,Option.pure_def,Option.some.injEq] at hm
    subst ms
    obtain ⟨bits,hbits⟩ := repeated_word_head r h ht
    have hbits' : (portWord r xs).map z++[z q] = z (cross r h out)::bits.map z := by
      simpa using congrArg (List.map z) hbits
    have hi := ih rfl tail hcap
    rw [hbits'] at hi
    simp only [portWord,ho,Option.toList_some,List.cons_append,List.nil_append,List.map_cons,
      List.map_append,hbits',rightValue]
    rw [binaryTable_at_assignment r vertex coeff z p out ho,
      edgeTable_at_assignment r h edge coeff z out,hi]
    simp only [walkWeight,departures,ho,Option.toList_some,List.cons_append,List.nil_append,
      List.map_cons,List.prod_cons,List.filterMap_cons,ho,vertexWeight,edgeWeight]
    ac_rfl

end Holant.LocalDrafts.TraversalCompletion.ArityTwo
