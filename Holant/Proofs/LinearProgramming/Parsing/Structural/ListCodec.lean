import Holant.Proofs.LinearProgramming.Parsing.FramePrefix
import Holant.Complexity.GraphPreprocessing.ListScan

/-! Literal image theorems for the OLD framed word-list codec.
Fuel is exactly the received input length. This file is only a mathematical
specification adapter, not a parser-machine instruction or decoding oracle. -/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Structural.WordList
open Computability Holant.Algebraic Holant.Complexity GraphPreprocessing
abbrev encoding := framedListEncoding Frame.wordEncoding

theorem prefix_some (fuel : ℕ) (input : List Bool) (xs : List (List Bool)) (suffix : List Bool)
    (h : framedListDecodePrefix Frame.wordEncoding fuel input=some (xs,suffix)) :
    input=framedListEncode Frame.wordEncoding xs++suffix := by
  induction fuel generalizing input xs suffix with
  | zero => simp [framedListDecodePrefix] at h
  | succ fuel ih =>
    cases input with
    | nil => simp [framedListDecodePrefix] at h
    | cons bit rest =>
      cases bit with
      | false =>
        have hp : ([],rest)=(xs,suffix) := Option.some.inj h
        have hx : ([] : List (List Bool))=xs := congrArg Prod.fst hp
        have hs : rest=suffix := congrArg Prod.snd hp
        rw [←hx,←hs]
        rfl
      | true =>
        cases hu : unframe rest with
        | none => simp [framedListDecodePrefix,hu] at h
        | some p =>
          rw [framedListDecodePrefix,hu] at h
          change ((framedListDecodePrefix Frame.wordEncoding fuel p.2).bind
            (fun q => some (p.1::q.1,q.2)))=some (xs,suffix) at h
          cases ht : framedListDecodePrefix Frame.wordEncoding fuel p.2 with
          | none => simp [ht] at h
          | some q =>
            have hp : (p.1::q.1,q.2)=(xs,suffix) := by
              simpa only [ht,Option.bind_some,
                Option.some.injEq] using h
            have hx : p.1::q.1=xs := congrArg Prod.fst hp
            have hs : q.2=suffix := congrArg Prod.snd hp
            rw [←hx,←hs]
            have heq : rest=frame p.1++p.2 := (Frame.unframe_some_iff rest p.1 p.2).mp hu
            rw [heq,ih p.2 q.1 q.2 ht]
            change true::(frame p.1++(framedListEncode Frame.wordEncoding q.1++q.2))=
              (true::(frame p.1++framedListEncode Frame.wordEncoding q.1))++q.2
            simp only [List.append_assoc,List.cons_append]

theorem decode_some_iff (input : List Bool) (xs : List (List Bool)) :
    encoding.decode input=some xs ↔ input=encoding.encode xs := by
  constructor
  · intro h
    change (framedListDecodePrefix Frame.wordEncoding input.length input).bind
      (fun p => if p.2=[] then some p.1 else none)=some xs at h
    obtain ⟨p,hp,hlast⟩ := Option.bind_eq_some_iff.mp h
    by_cases hs : p.2=[]
    · have hx : p.1=xs := by simpa only [hs,ite_true,Option.some.injEq] using hlast
      change input=framedListEncode Frame.wordEncoding xs
      simpa only [hs,hx,List.append_nil] using prefix_some input.length input p.1 p.2 hp
    · simp only [hs,ite_false] at hlast
      cases hlast
  · intro h
    rw [h]
    exact encoding.decode_encode xs

theorem decode_none_iff (input : List Bool) :
    encoding.decode input=none ↔ ¬ ∃ xs, input=encoding.encode xs := by
  constructor
  · intro hd ⟨xs,hxs⟩
    have hs := (decode_some_iff input xs).mpr hxs
    rw [hd] at hs
    cases hs
  · intro h
    cases hd : encoding.decode input with
    | none => rfl
    | some xs => exact False.elim (h ⟨xs,(decode_some_iff input xs).mp hd⟩)

theorem false_image (rest : List Bool) :
    (∃ xs, false::rest=encoding.encode xs) ↔ rest=[] := by
  constructor
  · rintro ⟨xs,h⟩
    cases xs with
    | nil => exact (List.cons.inj h).2
    | cons word xs => cases (List.cons.inj h).1
  · rintro rfl
    exact ⟨[],rfl⟩

theorem cons_image (word rest : List Bool) :
    (∃ xs, true::(frame word++rest)=encoding.encode xs) ↔ ∃ xs, rest=encoding.encode xs := by
  constructor
  · rintro ⟨xs,h⟩
    cases xs with
    | nil => cases (List.cons.inj h).1
    | cons head xs =>
      have he : frame word++rest=frame head++encoding.encode xs := (List.cons.inj h).2
      have hu := congrArg unframe he
      simp only [unframe_frame_append] at hu
      exact ⟨xs,congrArg Prod.snd (Option.some.inj hu)⟩
  · rintro ⟨xs,rfl⟩
    exact ⟨word::xs,rfl⟩

theorem malformed_frame (rest : List Bool) (hu : unframe rest=none) :
    ¬ ∃ xs, true::rest=encoding.encode xs := by
  rintro ⟨xs,h⟩
  cases xs with
  | nil => cases (List.cons.inj h).1
  | cons word xs =>
    have he : rest=frame word++encoding.encode xs := (List.cons.inj h).2
    rw [he,unframe_frame_append] at hu
    cases hu
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Structural.WordList
