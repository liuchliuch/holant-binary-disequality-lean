import Holant.OneHot.StackProgram.Tree
import Holant.Complexity.FramedEncoding

/-! Faithful literal encodings of ordered labelled trees and forests. This
module was reconstructed after workspace replacement with the established
byte grammar. Prefix decoders use actual finite fuel and retain every suffix. -/

namespace Holant.OneHot.StackProgram.TreeEncoding
open Computability Holant.Algebraic
variable {A : Type} (e : Encoding A Bool)

mutual
def treeEncode : Tree A → List Bool
  | .node a b ts => frame (e.encode a) ++ frame (e.encode b) ++ forestEncode ts
def forestEncode : Forest A → List Bool
  | .nil => [false]
  | .cons p t ts => true :: (frame (e.encode p) ++ treeEncode t ++ forestEncode ts)
end

mutual
def treeFuel : Tree A → ℕ
  | .node _ _ ts => 1 + forestFuel ts
def forestFuel : Forest A → ℕ
  | .nil => 1
  | .cons _ t ts => 1 + treeFuel t + forestFuel ts
end

mutual
def treeDecodePrefix : ℕ → List Bool → Option (Tree A × List Bool)
  | 0, _ => none
  | fuel + 1, bits => do
      let (aw,rest) ← unframe bits
      let a ← e.decode aw
      let (bw,rest) ← unframe rest
      let b ← e.decode bw
      let (ts,suffix) ← forestDecodePrefix fuel rest
      pure (.node a b ts,suffix)
def forestDecodePrefix : ℕ → List Bool → Option (Forest A × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: suffix => some (.nil,suffix)
  | fuel + 1, true :: bits => do
      let (pw,rest) ← unframe bits
      let p ← e.decode pw
      let (t,rest) ← treeDecodePrefix fuel rest
      let (ts,suffix) ← forestDecodePrefix fuel rest
      pure (.cons p t ts,suffix)
end

mutual
theorem treeDecodePrefix_encode (e : Encoding A Bool) (t : Tree A) (suffix : List Bool) (fuel : ℕ)
    (hf : treeFuel t ≤ fuel) :
    treeDecodePrefix e fuel (treeEncode e t ++ suffix) = some (t,suffix) := by
  cases t with
  | node a b ts =>
    cases fuel with
    | zero => simp [treeFuel] at hf
    | succ fuel =>
      have hs : forestFuel ts ≤ fuel := by simp only [treeFuel] at hf; omega
      simp [treeEncode,treeDecodePrefix,List.append_assoc,forestDecodePrefix_encode e ts suffix fuel hs]
theorem forestDecodePrefix_encode (e : Encoding A Bool) (ts : Forest A) (suffix : List Bool) (fuel : ℕ)
    (hf : forestFuel ts ≤ fuel) :
    forestDecodePrefix e fuel (forestEncode e ts ++ suffix) = some (ts,suffix) := by
  cases ts with
  | nil =>
    cases fuel with
    | zero => simp [forestFuel] at hf
    | succ fuel => rfl
  | cons p t ts =>
    cases fuel with
    | zero => simp [forestFuel] at hf
    | succ fuel =>
      have ht : treeFuel t ≤ fuel := by simp only [forestFuel] at hf; omega
      have hs : forestFuel ts ≤ fuel := by simp only [forestFuel] at hf; omega
      simp [forestEncode,forestDecodePrefix,List.append_assoc,
        treeDecodePrefix_encode e t (forestEncode e ts ++ suffix) fuel ht,
        forestDecodePrefix_encode e ts suffix fuel hs]
end

mutual
theorem treeFuel_le_length (e : Encoding A Bool) (t : Tree A) : treeFuel t ≤ (treeEncode e t).length := by
  cases t with
  | node a b ts =>
    have h := forestFuel_le_length e ts
    simp only [treeFuel,treeEncode,List.length_append,frame_length]
    omega
theorem forestFuel_le_length (e : Encoding A Bool) (ts : Forest A) : forestFuel ts ≤ (forestEncode e ts).length := by
  cases ts with
  | nil => rfl
  | cons p t ts =>
    have ht := treeFuel_le_length e t
    have hs := forestFuel_le_length e ts
    simp only [forestFuel,forestEncode,List.length_cons,List.length_append,frame_length]
    omega
end

def treeDecode (bits : List Bool) : Option (Tree A) :=
  (treeDecodePrefix e bits.length bits).bind (fun p => if p.2 = [] then some p.1 else none)
def forestDecode (bits : List Bool) : Option (Forest A) :=
  (forestDecodePrefix e bits.length bits).bind (fun p => if p.2 = [] then some p.1 else none)

@[simp] theorem treeDecode_encode (t : Tree A) : treeDecode e (treeEncode e t) = some t := by
  have h := treeDecodePrefix_encode e t [] (treeEncode e t).length (treeFuel_le_length e t)
  simp only [List.append_nil] at h
  simp [treeDecode,h]
@[simp] theorem forestDecode_encode (ts : Forest A) : forestDecode e (forestEncode e ts) = some ts := by
  have h := forestDecodePrefix_encode e ts [] (forestEncode e ts).length (forestFuel_le_length e ts)
  simp only [List.append_nil] at h
  simp [forestDecode,h]

def treeEncoding : Encoding (Tree A) Bool where
  encode := treeEncode e
  decode := treeDecode e
  decode_encode := treeDecode_encode e

def forestEncoding : Encoding (Forest A) Bool where
  encode := forestEncode e
  decode := forestDecode e
  decode_encode := forestDecode_encode e

mutual
theorem treeEncode_length_le (e : Encoding A Bool) (C : ℕ)
    (hc : ∀ a, (e.encode a).length ≤ C) (t : Tree A) :
    (treeEncode e t).length ≤ (4*C+3)*t.vertices + (2*C+2)*t.edges := by
  cases t with
  | node a b ts =>
    have ha := hc a
    have hb := hc b
    have hs := forestEncode_length_le e C hc ts
    simp only [treeEncode,List.length_append,frame_length,Tree.vertices,Tree.edges,
      Nat.mul_add,Nat.mul_one]
    omega
theorem forestEncode_length_le (e : Encoding A Bool) (C : ℕ)
    (hc : ∀ a, (e.encode a).length ≤ C) (ts : Forest A) :
    (forestEncode e ts).length ≤ (4*C+3)*ts.vertices + (2*C+2)*ts.edges + 1 := by
  cases ts with
  | nil => simp [forestEncode,Forest.vertices,Forest.edges]
  | cons p t ts =>
    have hp := hc p
    have ht := treeEncode_length_le e C hc t
    have hs := forestEncode_length_le e C hc ts
    simp only [forestEncode,List.length_cons,List.length_append,frame_length,
      Forest.vertices,Forest.edges,Nat.mul_add,Nat.mul_one]
    omega
end

end Holant.OneHot.StackProgram.TreeEncoding
