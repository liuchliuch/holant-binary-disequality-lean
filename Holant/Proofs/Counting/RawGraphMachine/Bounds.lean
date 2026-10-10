import Holant.Proofs.Counting.RawGraphMachine.Stages


set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Holant.LocalDrafts.CountingHardness.RawGraphMachine.Bounds
open Computability Holant.Complexity FixedGadgetSubstitution
open BinaryCompose FixedFieldMachines GraphPreprocessing

variable {A : Type}
def width (s : Work) := (workEncoding.encode s).length
def points (B : ℕ) (s : Memory) : Prop := ∀ p ∈ s.1, (endpointEncoding.encode p).length ≤ B

theorem list_cons (e : Encoding A Bool) (x : A) (xs : List A) :
    ((framedListEncoding e).encode (x :: xs)).length =
      2 * (e.encode x).length + 2 + ((framedListEncoding e).encode xs).length := by
  simp only [framedListEncoding, framedListEncode, List.length_cons, List.length_append,
    Holant.Algebraic.frame_length]
  omega

theorem list_append (e : Encoding A Bool) (xs ys : List A) :
    ((framedListEncoding e).encode (xs ++ ys)).length + 1 =
      ((framedListEncoding e).encode xs).length + ((framedListEncoding e).encode ys).length := by
  induction xs with
  | nil => simp [framedListEncoding, framedListEncode, Nat.add_comm]
  | cons x xs ih => simp only [List.cons_append, list_cons]; omega

theorem list_set (e : Encoding A Bool) (xs : List A) (i : ℕ) (a : A) :
    ((framedListEncoding e).encode (xs.set i a)).length ≤
      ((framedListEncoding e).encode xs).length + 2 * (e.encode a).length := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.set_cons_zero, list_cons]; omega
    | succ i => simpa only [List.set_cons_succ, list_cons, Nat.add_assoc] using
        Nat.add_le_add_left (ih i) (2 * (e.encode x).length + 2)

theorem member_length (e : Encoding A Bool) (xs : List A) (a : A) (ha : a ∈ xs) :
    (e.encode a).length ≤ ((framedListEncoding e).encode xs).length := by
  revert ha
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro ha
    rw [list_cons]
    rcases List.mem_cons.mp ha with h | h
    · subst a; omega
    · have := ih h; omega

theorem set_points (B : ℕ) (xs : List RawEndpoint) (i : ℕ) (a : RawEndpoint)
    (hx : ∀ p ∈ xs, (endpointEncoding.encode p).length ≤ B)
    (ha : (endpointEncoding.encode a).length ≤ B) :
    ∀ p ∈ xs.set i a, (endpointEncoding.encode p).length ≤ B := by
  intro p hp
  rcases List.mem_or_eq_of_mem_set hp with hp | rfl
  · exact hx p hp
  · exact ha

theorem read_bound (B : ℕ) (xs : List RawEndpoint) (i : ℕ) (hB : 2 ≤ B)
    (hx : ∀ p ∈ xs, (endpointEncoding.encode p).length ≤ B) :
    (endpointEncoding.encode (xs.getD i (0, false))).length ≤ B := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hx _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact (endpoint_length_le (0, false) 0 (by simp)).trans hB

theorem row_bound (B : ℕ) (tag : ℕ) (ps : List RawEndpoint) (ht : tag ≤ 4)
    (hl : ps.length ≤ 3) (hp : ∀ p ∈ ps, (endpointEncoding.encode p).length ≤ B) :
    (vertexEncoding.encode (tag, ps)).length ≤ 6 * B + 16 := by
  have hn := (nat_code_length_le tag).trans ht
  have hps := framedList_length_le endpointEncoding ps B hp
  change (RawClosedNetwork.vertexEncoding.encode (tag, ps)).length ≤ _
  rw [RawClosedNetwork.vertexEncoding, framedProductEncoding_length]
  change 2 * (encodingNatBool.encode tag).length + 1 +
    (framedListEncode endpointEncoding ps).length ≤ _
  have hm := Nat.mul_le_mul_left (2 * B + 2) hl
  nlinarith

theorem memory_length (s : Memory) : (memoryEncoding.encode s).length =
    2 * (envEncoding.encode s.1).length + 2 * s.2.1 + (verticesEncoding.encode s.2.2).length + 2 := by
  simp only [memoryEncoding, pairEncoding_length, Access.unary,
    VerifierCompiler.Stateful.CapacityFrontend.Unary.encoding,
    Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters.unary, UnaryBinary.unaryEncoding,
    List.length_replicate]
  omega

theorem work_length (s : Work) : width s =
    4 * ((framedListEncoding Circuit.rowEncoding).encode s.1.1).length +
      2 * (encodingNatBool.encode s.1.2).length + (memoryEncoding.encode s.2).length + 3 := by
  simp only [width, workEncoding, Circuit.codeEncoding, pairEncoding_length, framedProductEncoding_length]
  omega

theorem gate_offset (s : Memory) (r : Circuit.Row) : (gate s r).2.1 ≤ s.2.1 + 5 := by
  by_cases h : r.1 < 2 <;> simp [gate, h, constant, nand] <;> omega

theorem gate_points (B : ℕ) (s : Memory) (r : Circuit.Row) (hp : points B s)
    (hf : ∀ k ≤ 4, ∀ sign, (endpointEncoding.encode (s.2.1 + k, sign)).length ≤ B) :
    points B (gate s r) := by
  have h₀ := hf 0 (by omega) true
  have h₂ := hf 2 (by omega) true
  have h₄ := hf 4 (by omega) true
  simp only [Nat.add_zero] at h₀
  by_cases h : r.1 < 2
  · simpa [gate, h, constant, points] using And.intro h₀ hp
  · have h₁ := set_points B s.1 r.2.1 (s.2.1, true) hp h₀
    have h₂' := set_points B _ r.2.2 (s.2.1 + 2, true) h₁ h₂
    simpa [gate, h, nand, points] using And.intro h₄ h₂'

/-- A concrete linear increase per round, not an assumed intermediate-size
certificate. It counts both updates and all three framed emitted vertices. -/
theorem gate_width (B : ℕ) (s : Memory) (r : Circuit.Row) (hB : 2 ≤ B)
    (hp : points B s)
    (hf : ∀ k ≤ 4, ∀ sign, (endpointEncoding.encode (s.2.1 + k, sign)).length ≤ B) :
    (memoryEncoding.encode (gate s r)).length ≤
      (memoryEncoding.encode s).length + 48 * B + 128 := by
  have h₀ := hf 0 (by omega) true
  have h₀f := hf 0 (by omega) false
  simp only [Nat.add_zero] at h₀ h₀f
  by_cases h : r.1 < 2
  · let tag : ℕ := if decide (r.1 = 1) then 2 else 1
    have ht : tag ≤ 4 := by dsimp [tag]; split <;> omega
    have hv := row_bound B tag [(s.2.1, false)] ht (by simp)
      (by simpa using h₀f)
    have he := list_cons endpointEncoding (s.2.1, true) s.1
    have ha := list_append vertexEncoding s.2.2 [(tag, [(s.2.1, false)])]
    have hn := list_cons vertexEncoding (tag, [(s.2.1, false)]) []
    change (verticesEncoding.encode [(tag, [(s.2.1, false)])]).length =
      2 * (vertexEncoding.encode (tag, [(s.2.1, false)])).length + 2 + 1 at hn
    rw [memory_length, memory_length]
    simp only [gate, if_pos h, constant]
    change 2 * (envEncoding.encode ((s.2.1, true) :: s.1)).length +
      2 * (s.2.1 + 1) + (verticesEncoding.encode (s.2.2 ++ [(tag, [(s.2.1, false)])])).length + 2 ≤ _
    dsimp only [envEncoding, verticesEncoding] at *
    omega
  · let e₁ := s.1.set r.2.1 (s.2.1, true)
    let e₂ := e₁.set r.2.2 (s.2.1 + 2, true)
    have hp₁ := set_points B s.1 r.2.1 (s.2.1, true) hp h₀
    have hr₁ := read_bound B s.1 r.2.1 hB hp
    have hr₂ := read_bound B e₁ r.2.2 hB hp₁
    have h₁ := list_set endpointEncoding s.1 r.2.1 (s.2.1, true)
    have h₂ := list_set endpointEncoding e₁ r.2.2 (s.2.1 + 2, true)
    have hpush := list_cons endpointEncoding (s.2.1 + 4, true) e₂
    let vs : List RawVertex :=
      [(3, [s.1.getD r.2.1 (0, false), (s.2.1, false), (s.2.1 + 1, false)]),
        (3, [e₁.getD r.2.2 (0, false), (s.2.1 + 2, false), (s.2.1 + 3, false)]),
        (4, [(s.2.1 + 1, true), (s.2.1 + 3, true), (s.2.1 + 4, false)])]
    have hv : ∀ v ∈ vs, (vertexEncoding.encode v).length ≤ 6 * B + 16 := by
      intro v hv
      simp only [vs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · apply row_bound B 3 _ (by omega) (by simp)
        simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil, false_implies, implies_true, and_true]
        exact ⟨hr₁, h₀f, hf 1 (by omega) false⟩
      · apply row_bound B 3 _ (by omega) (by simp)
        simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil, false_implies, implies_true, and_true]
        exact ⟨hr₂, hf 2 (by omega) false, hf 3 (by omega) false⟩
      · apply row_bound B 4 _ (by omega) (by simp)
        simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil, false_implies, implies_true, and_true]
        exact ⟨hf 1 (by omega) true, hf 3 (by omega) true, hf 4 (by omega) false⟩
    have hvs := framedList_length_le vertexEncoding vs (6 * B + 16) hv
    have ha := list_append vertexEncoding s.2.2 vs
    have hf₂ := hf 2 (by omega) true
    have hf₄ := hf 4 (by omega) true
    rw [memory_length, memory_length]
    simp only [gate, if_neg h, nand]
    change 2 * (envEncoding.encode ((s.2.1 + 4, true) :: e₂)).length +
      2 * (s.2.1 + 5) + (verticesEncoding.encode (s.2.2 ++ vs)).length + 2 ≤ _
    change ((framedListEncoding endpointEncoding).encode e₁).length ≤ _ at h₁
    change ((framedListEncoding endpointEncoding).encode e₂).length ≤ _ at h₂
    have hlen : vs.length = 3 := rfl
    rw [hlen] at hvs
    dsimp only [envEncoding, verticesEncoding, framedListEncoding] at *
    omega

theorem advance_offset (s : Work) : (advance s).2.2.1 ≤ s.2.2.1 + 5 := by
  rcases s with ⟨⟨rs, out⟩, m⟩
  cases rs with
  | nil => simp [advance]
  | cons r rs => exact gate_offset m r

theorem advance_points (B : ℕ) (s : Work) (hp : points B s.2)
    (hf : ∀ k ≤ 4, ∀ sign, (endpointEncoding.encode (s.2.2.1 + k, sign)).length ≤ B) :
    points B (advance s).2 := by
  rcases s with ⟨⟨rs, out⟩, m⟩
  cases rs with
  | nil => exact hp
  | cons r rs => exact gate_points B m r hp hf

theorem advance_width (B : ℕ) (s : Work) (hB : 2 ≤ B) (hp : points B s.2)
    (hf : ∀ k ≤ 4, ∀ sign, (endpointEncoding.encode (s.2.2.1 + k, sign)).length ≤ B) :
    width (advance s) ≤ width s + 48 * B + 128 := by
  rcases s with ⟨⟨rs, out⟩, m⟩
  cases rs with
  | nil => simp only [advance]; omega
  | cons r rs =>
    have h := gate_width B m r hB hp hf
    simp only [advance, work_length, list_cons]
    omega

theorem offset_le_width (s : Work) : s.2.2.1 ≤ width s := by
  rw [work_length, memory_length]; omega

theorem points_le_width (s : Work) : points (width s) s.2 := by
  intro p hp
  have h := member_length endpointEncoding s.2.1 p hp
  rw [work_length, memory_length]
  dsimp only [envEncoding] at *
  omega

theorem iterate_invariant (s : Work) (i : ℕ) (hi : i ≤ width s) :
    ((advance^[i]) s).2.2.1 ≤ width s + 5 * i ∧
      points (12 * width s + 12) ((advance^[i]) s).2 ∧
      width ((advance^[i]) s) ≤ width s + i * (48 * (12 * width s + 12) + 128) := by
  revert hi
  induction i with
  | zero =>
    intro hi
    refine ⟨by simpa using offset_le_width s, ?_, by simp⟩
    intro p hp
    have h := points_le_width s p hp
    simpa using (show (endpointEncoding.encode p).length ≤ 12 * width s + 12 by omega)
  | succ i ih =>
    intro hi
    obtain ⟨ho, hp, hw⟩ := ih (by omega)
    have hf : ∀ k ≤ 4, ∀ sign,
        (endpointEncoding.encode (((advance^[i]) s).2.2.1 + k, sign)).length ≤ 12 * width s + 12 := by
      intro k hk sign
      have h := endpoint_length_le (((advance^[i]) s).2.2.1 + k, sign)
        (6 * width s + 4) (by dsimp; omega)
      change (endpointEncoding.encode _).length ≤ _ at h
      omega
    have hn := advance_offset ((advance^[i]) s)
    have hpoints := advance_points (12 * width s + 12) ((advance^[i]) s) hp hf
    have hwidth := advance_width (12 * width s + 12) ((advance^[i]) s) (by omega) hp hf
    simp only [Function.iterate_succ_apply']
    refine ⟨by omega, hpoints, ?_⟩
    rw [Nat.succ_mul]
    omega

noncomputable def storagePolynomial : Polynomial ℕ := 2000 * (Polynomial.X + 1) ^ 2

theorem iterate_width (s : Work) (i : ℕ) (hi : i ≤ width s) :
    width ((advance^[i]) s) ≤ storagePolynomial.eval (width s) := by
  have h := (iterate_invariant s i hi).2.2
  have hm := Nat.mul_le_mul_right (48 * (12 * width s + 12) + 128) hi
  simp only [storagePolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

theorem width_le_storage (n : ℕ) : n ≤ storagePolynomial.eval n := by
  simp only [storagePolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

end Holant.LocalDrafts.CountingHardness.RawGraphMachine.Bounds
