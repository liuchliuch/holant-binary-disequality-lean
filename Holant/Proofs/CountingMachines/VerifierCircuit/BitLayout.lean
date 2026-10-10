import Holant.Proofs.CountingMachines.VerifierCircuit.FiniteBits
import Holant.Proofs.CountingMachines.VerifierCircuit.PackedStep

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# One-hot coordinates with an explicit linear-sized layout

Ported reference proof. See the task validation reports.

The finite choices below depend only on the fixed machine. The variable cell
indices are explicitly `List.finRange (C+1)`, never an enumeration of tapes.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.BitLayout


open Turing
open scoped Classical

variable (tm : FinTM2) (C : ℕ)
variable [∀ k, Fintype (tm.Γ k)]

abbrev Address := Option tm.Λ ⊕ (tm.σ ⊕ (Σ k : tm.K, Fin (C + 1) × Option (tm.Γ k)))
abbrev Bits := Address tm C → Bool

def labelAddr (l : Option tm.Λ) : Address tm C := .inl l
def stateAddr (s : tm.σ) : Address tm C := .inr (.inl s)
def cellAddr (k : tm.K) (i : Fin (C + 1)) (a : Option (tm.Γ k)) : Address tm C :=
  .inr (.inr ⟨k, i, a⟩)

def addresses : List (Address tm C) :=
  (fixedEnum (Option tm.Λ)).map (labelAddr tm C) ++
  (fixedEnum tm.σ).map (stateAddr tm C) ++
  (fixedEnum tm.K).flatMap (fun k =>
    (List.finRange (C + 1)).flatMap (fun i =>
      (fixedEnum (Option (tm.Γ k))).map (cellAddr tm C k i)))

theorem mem_addresses (a : Address tm C) : a ∈ addresses tm C := by
  cases a with
  | inl l => simp [addresses, labelAddr, mem_fixedEnum]
  | inr a =>
    cases a with
    | inl s => simp [addresses, stateAddr, mem_fixedEnum]
    | inr a =>
      rcases a with ⟨k, i, a⟩
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨k, mem_fixedEnum k, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨i, by simp, ?_⟩
      exact List.mem_map.mpr ⟨a, mem_fixedEnum a, rfl⟩

def controlWidth : ℕ := Fintype.card (Option tm.Λ) + Fintype.card tm.σ
def cellWidth : ℕ := ((fixedEnum tm.K).map (fun k => Fintype.card (Option (tm.Γ k)))).sum

theorem addresses_length : (addresses tm C).length = controlWidth tm + (C + 1) * cellWidth tm := by
  have hs : ∀ ks : List tm.K,
      (ks.flatMap (fun k => (List.finRange (C + 1)).flatMap (fun i =>
        (fixedEnum (Option (tm.Γ k))).map (cellAddr tm C k i)))).length =
      (C + 1) * (ks.map (fun k => Fintype.card (Option (tm.Γ k)))).sum := by
    intro ks
    induction ks with
    | nil => simp
    | cons k ks ih =>
      simp [List.flatMap_cons, ih, List.length_flatMap, Nat.mul_add, Nat.mul_comm]
  simp only [addresses, List.length_append, List.length_map, fixedEnum_length, hs]
  rfl

def encode (p : PackedStep.Packed tm C) : Bits tm C
  | .inl l => oneHot p.1 l
  | .inr (.inl s) => oneHot p.2.1 s
  | .inr (.inr ⟨k, i, a⟩) => oneHot (p.2.2 k i) a

theorem encode_injective : Function.Injective (encode tm C) := by
  intro p q h
  apply Prod.ext
  · apply oneHot_injective
    funext l
    exact congrFun h (labelAddr tm C l)
  · apply Prod.ext
    · apply oneHot_injective
      funext s
      exact congrFun h (stateAddr tm C s)
    · funext k i
      apply oneHot_injective
      funext a
      exact congrFun h (cellAddr tm C k i a)

def replaceState (x : Bits tm C) (s : tm.σ → Bool) : Bits tm C
  | .inr (.inl v) => s v
  | a => x a

def replaceLabel (x : Bits tm C) (l : Option tm.Λ → Bool) : Bits tm C
  | .inl v => l v
  | a => x a

def replacePush (x : Bits tm C) (k : tm.K) (head : Option (tm.Γ k) → Bool) : Bits tm C
  | .inr (.inr ⟨j, i, a⟩) =>
    if h : j = k then
      if hi : i.val = 0 then head (h ▸ a)
      else x (cellAddr tm C j ⟨i.val - 1, by omega⟩ a)
    else x (cellAddr tm C j i a)
  | a => x a

def replacePop (x : Bits tm C) (k : tm.K) : Bits tm C
  | .inr (.inr ⟨j, i, a⟩) =>
    if j = k then
      if hi : i.val + 1 < C + 1 then x (cellAddr tm C j ⟨i.val + 1, hi⟩ a)
      else oneHot (none : Option (tm.Γ j)) a
    else x (cellAddr tm C j i a)
  | a => x a

theorem replaceState_encode (p : PackedStep.Packed tm C) (s : tm.σ) :
    replaceState tm C (encode tm C p) (oneHot s) = encode tm C (PackedStep.state tm C p s) := by
  funext a
  cases a with
  | inl a => rfl
  | inr a => cases a <;> rfl

theorem replaceLabel_encode (p : PackedStep.Packed tm C) (l : Option tm.Λ) :
    replaceLabel tm C (encode tm C p) (oneHot l) = encode tm C (PackedStep.label tm C p l) := by
  funext a
  cases a with
  | inl a => rfl
  | inr a => cases a <;> rfl

theorem replacePush_encode (p : PackedStep.Packed tm C) (k : tm.K) (v : tm.Γ k) :
    replacePush tm C (encode tm C p) k (oneHot (some v)) =
      encode tm C (PackedStep.push tm C p k v) := by
  funext a
  cases a with
  | inl a => rfl
  | inr a =>
    cases a with
    | inl a => rfl
    | inr a =>
      rcases a with ⟨j, i, a⟩
      by_cases hj : j = k
      · subst j
        by_cases hi : i.val = 0 <;>
          simp [replacePush, encode, PackedStep.push, PackedStep.shiftPush, cellAddr, hi]
      · simp [replacePush, encode, PackedStep.push, cellAddr, hj]

theorem replacePop_encode (p : PackedStep.Packed tm C) (k : tm.K) :
    replacePop tm C (encode tm C p) k = encode tm C (PackedStep.pop tm C p k) := by
  funext a
  cases a with
  | inl a => rfl
  | inr a =>
    cases a with
    | inl a => rfl
    | inr a =>
      rcases a with ⟨j, i, a⟩
      by_cases hj : j = k
      · subst j
        by_cases hi : i.val + 1 < C + 1 <;>
          simp [replacePop, encode, PackedStep.pop, PackedStep.shiftPop, cellAddr, hi]
      · simp [replacePop, encode, PackedStep.pop, cellAddr, hj]

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.BitLayout
