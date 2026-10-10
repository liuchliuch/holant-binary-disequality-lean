import Holant.Proofs.LinearProgramming.Support.Infrastructure.FiniteRun

/-!
Physical finite iteration, using the existing bitmap counter/call/cleanup
program. Its counter is constructed from input BYTES. The rapidly growing
resource recurrence below is proved from subprogram transitions, not a unit
cost assumption for rational arithmetic. No polynomial claim is made.
-/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.Iterate
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient StackProtocol
open FixedGadgetSubstitution.Compiler
variable {A : Type} (ea : Encoding A Bool) (next : A → A) (w : FiniteComputes ea ea next)

def wrapped : Encoding A Bool where
  encode x := frame (ea.encode x)
  decode bs := do
    let (word,rest) ← unframe bs
    if rest = [] then ea.decode word else none
  decode_encode a := by
    have hf : unframe (frame (ea.encode a)) = some (ea.encode a,[]) := by
      simpa only [List.append_nil] using unframe_frame_append (ea.encode a) []
    simp [hf,ea.decode_encode]

def value (s : A) : A := (next^[(ea.encode s).length]) s

noncomputable section
def provider : FiniteComputes (pairEncoding ea Frame.wordEncoding) ea (fun x => next x.1) :=
  (FiniteComputes.ofPoly (Wiring.firstComputes ea Frame.wordEncoding)).andThen w
def machine : Machine := BitmapIterate.machine (provider ea next w).machine
def advance (n : ℕ) : ℕ := (provider ea next w).width (2*n+1)
def grow (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k+1 => advance ea next w (grow n k)

theorem advance_mono : Monotone (advance ea next w) := by
  intro a b hab
  exact (provider ea next w).width_mono (by omega)
theorem le_advance (n : ℕ) : n ≤ advance ea next w n := by
  unfold advance FiniteComputes.width
  omega
theorem grow_base_mono (k : ℕ) : Monotone (fun n => grow ea next w n k) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih => exact (advance_mono ea next w).comp ih
theorem grow_count_mono (n : ℕ) : Monotone (grow ea next w n) :=
  monotone_nat_of_le_succ (fun k => le_advance ea next w _)
def width (n : ℕ) : ℕ := grow ea next w n n
theorem width_mono : Monotone (width ea next w) := by
  intro a b hab
  exact ((grow_base_mono ea next w a) hab).trans ((grow_count_mono ea next w b) hab)

theorem state_size (s : A) (n : ℕ) (hs : (ea.encode s).length ≤ n) (i : ℕ) :
    (ea.encode ((next^[i]) s)).length ≤ grow ea next w n i := by
  induction i with
  | zero => exact hs
  | succ i ih =>
    have h := (provider ea next w).output_length (((next^[i]) s), ([] : List Bool))
    simp only [pairEncoding_length, Frame.wordEncoding, List.length_nil, Nat.add_zero] at h
    rw [Function.iterate_succ_apply']
    apply h.trans
    unfold grow advance
    apply (provider ea next w).width_mono
    change 2*(ea.encode ((next^[i]) s)).length+1 ≤ 2*grow ea next w n i+1
    omega

def roundBound (n : ℕ) : ℕ :=
  (provider ea next w).time (2*width ea next w n+1) + 7*width ea next w n + 11
def time (n : ℕ) : ℕ := 5*n+8+n*roundBound ea next w n+2*width ea next w n+5
theorem roundBound_mono : Monotone (roundBound ea next w) := by
  intro a b hab
  have hw := width_mono ea next w hab
  have ht := (provider ea next w).time_mono (show 2*width ea next w a+1 ≤
    2*width ea next w b+1 by omega)
  unfold roundBound
  omega
theorem time_mono : Monotone (time ea next w) := by
  intro a b hab
  have hw := width_mono ea next w hab
  have ht := Nat.mul_le_mul hab (roundBound_mono ea next w hab)
  unfold time
  omega

/-- Exact trace length is explicit; no existential run length is chosen when
constructing the Type-valued timed-output witness. -/
def ticks (s : A) : ℕ → ℕ
  | 0 => 0
  | k+1 => ticks (next s) k + ((provider ea next w).outputs (s, ([] : List Bool))).steps +
      5*(ea.encode s).length+2*(ea.encode (next s)).length+11

set_option backward.isDefEq.respectTransparency false in
theorem loop_exact (s : A) (k : ℕ) :
    RunsExactly (machine ea next w).computer.step
      (BitmapIterate.ready (provider ea next w).machine
        (BitmapIterate.phase (provider ea next w).machine 5)
        (ea.encode s) [] (List.replicate k true) [] [] [])
      (BitmapIterate.ready (provider ea next w).machine
        (BitmapIterate.phase (provider ea next w).machine 5)
        (ea.encode ((next^[k]) s)) [] [] [] [] []) (ticks ea next w s k) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    let h := (provider ea next w).outputs (s, ([] : List Bool))
    have first := BitmapIterate.round_exact (provider ea next w).machine
      (ea.encode s) (List.replicate k true) [] [] (ea.encode (next s)) h.steps
      (by exact h.evals_in_steps)
    simpa only [machine, Machine.computer, FinTM2.step, BitmapIterate.machine, ticks, List.length_nil, Nat.mul_zero, Nat.add_zero,
      List.replicate_succ, Function.iterate_succ_apply, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.zero_add, h] using first.trans (ih (next s))

theorem ticks_bound (s : A) (n : ℕ) (hs : (ea.encode s).length ≤ n) (k i : ℕ)
    (hki : i+k ≤ n) : ticks ea next w ((next^[i]) s) k ≤ k*roundBound ea next w n := by
  induction k generalizing i with
  | zero => simp [ticks]
  | succ k ih =>
    let current := (next^[i]) s
    let result := next current
    let h := (provider ea next w).outputs (current, ([] : List Bool))
    have hc := (state_size ea next w s n hs i).trans
      (grow_count_mono ea next w n (by omega : i ≤ n))
    have hn := (state_size ea next w s n hs (i+1)).trans
      (grow_count_mono ea next w n (by omega : i+1 ≤ n))
    change (ea.encode current).length ≤ width ea next w n at hc
    change (ea.encode ((next^[i+1]) s)).length ≤ width ea next w n at hn
    have he : result = (next^[i+1]) s := by simp [result, current, Function.iterate_succ_apply']
    have hp : h.steps ≤ (provider ea next w).time (2*width ea next w n+1) := by
      apply h.steps_le_m.trans
      apply (provider ea next w).time_mono
      simp only [pairEncoding_length, Frame.wordEncoding, List.length_nil, Nat.add_zero]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 1
    have ht := ih (i+1) (by omega)
    have hb : h.steps+5*(ea.encode current).length+2*(ea.encode result).length+11 ≤
        roundBound ea next w n := by
      rw [he]
      unfold roundBound
      omega
    rw [← he] at ht
    change ticks ea next w result k + h.steps + 5*(ea.encode current).length +
      2*(ea.encode result).length + 11 ≤ _
    nlinarith

def wrappedComputes : FiniteComputes (wrapped ea) ea (value ea next) where
  machine := machine ea next w
  time := time ea next w
  time_mono := time_mono ea next w
  outputs s := by
    let L := (ea.encode s).length
    have ht : ticks ea next w s L ≤ L*roundBound ea next w L := by
      simpa using ticks_bound ea next w s L le_rfl L 0 (by omega)
    have core := loop_exact ea next w s L
    have prep := BitmapIterate.prepare (provider ea next w).machine (ea.encode s) []
    have last := BitmapIterate.finish (provider ea next w).machine
      (ea.encode ((next^[L]) s)) [] []
    have hn := state_size ea next w s L le_rfl L
    change (ea.encode ((next^[L]) s)).length ≤ width ea next w L at hn
    have all := (prep.trans core).trans last
    refine {
      steps := (2*(ea.encode ((next^[L]) s)).length+5)+(ticks ea next w s L+(5*L+8))
      evals_in_steps := ?_
      steps_le_m := ?_ }
    · change RunsExactly (machine ea next w).computer.step
        (initList (machine ea next w).computer ((wrapped ea).encode s))
        (haltList (machine ea next w).computer (ea.encode (value ea next s))) _
      unfold machine wrapped
      rw [BitmapIterate.initial]
      simpa only [machine, Machine.computer, FinTM2.step, BitmapIterate.machine, wrapped, value, List.length_nil, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, List.append_nil, L] using all
    · apply le_trans (show _ ≤ time ea next w L by unfold time; omega)
      apply time_mono ea next w
      simp only [wrapped, frame_length]
      omega

/-- The extra frame is physically produced by the existing byte serializer. -/
def computes : FiniteComputes ea ea (value ea next) := by
  let framing : Computes ea (wrapped ea) id := FixedFieldMachines.recode
    ((encodeComputes ea).andThen frameComputes) id (fun _ => rfl) (fun _ => rfl)
  exact (FiniteComputes.ofPoly framing).andThen (wrappedComputes ea next w)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.Iterate
