import Holant.Proofs.LinearProgramming.Parsing.PartialList.Codec

open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.BranchCode
open Computability
namespace Image
variable {A : Type} (ea : Encoding A Bool)
def decode (input : List Bool) : Option A :=
  (ea.decode input).bind (fun a => if ea.encode a=input then some a else none)
theorem some_iff (input : List Bool) (a : A) :
    decode ea input=some a ↔ input=ea.encode a := by
  constructor
  · intro h
    unfold decode at h
    cases hd : ea.decode input with
    | none => simp only [hd,Option.bind_none] at h; cases h
    | some b =>
      simp only [hd,Option.bind_some] at h
      split at h
      next he =>
        have hb : b=a := Option.some.inj h
        subst b
        exact he.symm
      next he => cases h
  · intro h
    rw [h]
    simp only [decode,Encoding.decode_encode,Option.bind_some,↓reduceIte]
def encoding : Encoding A Bool where
  encode := ea.encode
  decode := decode ea
  decode_encode a := (some_iff ea _ a).mpr rfl
theorem strict : PartialList.Strict (encoding ea) := some_iff ea
theorem none_iff (input : List Bool) :
    decode ea input=none ↔ ¬ ∃ a, input=ea.encode a := by
  constructor
  · intro h ⟨a,ha⟩
    have hs := (some_iff ea input a).mpr ha
    rw [h] at hs
    cases hs
  · intro h
    cases hd : decode ea input with
    | none => rfl
    | some a => exact False.elim (h ⟨a,(some_iff ea input a).mp hd⟩)

/-- This is a codec-image transport theorem, not a running decoder factory. -/
theorem eq_of_image {f : List Bool → Option A}
    (hf : ∀ input a, f input=some a ↔ input=ea.encode a) (input : List Bool) :
    f input=decode ea input := by
  cases h : f input with
  | some a => exact ((some_iff ea input a).mpr ((hf input a).mp h)).symm
  | none =>
    cases hd : decode ea input with
    | none => rfl
    | some a =>
      have he := (hf input a).mpr ((some_iff ea input a).mp hd)
      rw [h] at he
      cases he
end Image
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.BranchCode
