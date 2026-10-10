import Holant.ReedMuller.FlatNetwork.GenerationWeight
import Holant.ReedMuller.FlatNetwork.Relabel

/-! Finite programs made only from weight-four transvections and coordinate
permutations, with exact actions on binary codes and exact gate counts. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Adding one adjacent repetition pair to an arbitrary binary code. -/
def pairExtension (D : BinaryCode n) : BinaryCode (n+2) where
  carrier := {x | x 0 = x 1 ∧ dropTwo x ∈ D}
  zero_mem' := ⟨rfl, D.zero_mem⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨by change x 0 + y 0 = x 1 + y 1; rw [hx.1, hy.1], D.add_mem hx.2 hy.2⟩
  smul_mem' := fun c x hx => ⟨by change _ * _ = _ * _; rw [hx.1], D.smul_mem c hx.2⟩

@[simp] theorem mem_pairExtension (D : BinaryCode n) (x : BinaryVector (n+2)) :
    x ∈ pairExtension D ↔ x 0 = x 1 ∧ dropTwo x ∈ D := Iff.rfl

/-- The usual adjacent-pair repetition code; the odd branch is irrelevant to
self-dual codes and is included to make the family total. -/
def standardPairs : (n : ℕ) → BinaryCode n
  | 0 => ⊥
  | 1 => ⊥
  | n+2 => pairExtension (standardPairs n)

inductive GenerationGate (n : ℕ)
  | tau (s : BinaryVector n) (weight_four : binaryWeight s = 4)
  | perm (e : Fin n ≃ Fin n)

namespace GenerationGate

def applyCode : GenerationGate n → BinaryCode n → BinaryCode n
  | .tau s _ => transvectionCode s
  | .perm e => relabelCode e

def applyWord : GenerationGate n → BinaryVector n → BinaryVector n
  | .tau s _ => transvection s
  | .perm e => coordinateMap e.symm

def inverse : GenerationGate n → GenerationGate n
  | .tau s h => .tau s h
  | .perm e => .perm e.symm

theorem weightFour_isotropic (s : BinaryVector n) (h : binaryWeight s = 4) : dot s s = 0 := by
  rw [← cast_binaryWeight, h]
  decide

theorem mem_applyCode (g : GenerationGate n) (D : BinaryCode n) (x : BinaryVector n) :
    x ∈ g.applyCode D ↔ g.inverse.applyWord x ∈ D := by
  cases g with
  | tau s hs => exact mem_transvectionCode s (weightFour_isotropic s hs) D x
  | perm e => rfl

theorem applyWord_inverse (g : GenerationGate n) (x : BinaryVector n) :
    g.inverse.applyWord (g.applyWord x) = x := by
  cases g with
  | tau s hs => exact transvection_involutive s (weightFour_isotropic s hs) x
  | perm e => funext i; simp [applyWord, inverse, coordinateMap]

@[simp] theorem inverse_inverse (g : GenerationGate n) : g.inverse.inverse = g := by
  cases g <;> rfl

theorem applyCode_inverse (g : GenerationGate n) (D : BinaryCode n) :
    g.inverse.applyCode (g.applyCode D) = D := by
  ext x
  rw [mem_applyCode, mem_applyCode, inverse_inverse, applyWord_inverse]

/-- Every primitive's code action is exactly the image of its literal word action. -/
theorem applyCode_image (g : GenerationGate n) (D : BinaryCode n) (x : BinaryVector n) :
    x ∈ g.applyCode D ↔ ∃ y ∈ D, g.applyWord y = x := by
  rw [mem_applyCode]
  constructor
  · intro hx
    refine ⟨g.inverse.applyWord x, hx, ?_⟩
    simpa only [inverse_inverse] using applyWord_inverse g.inverse x
  · rintro ⟨y, hy, rfl⟩
    rwa [applyWord_inverse]

theorem preserves_selfDual (g : GenerationGate n) (D : BinaryCode n) (hD : SelfDual D) :
    SelfDual (g.applyCode D) := by
  cases g with
  | tau s hs => exact transvectionCode_selfDual s (weightFour_isotropic s hs) D hD
  | perm e => exact relabelCode_selfDual e D hD

end GenerationGate

abbrev GenerationProgram (n : ℕ) := List (GenerationGate n)

namespace GenerationProgram

def run : GenerationProgram n → BinaryCode n → BinaryCode n
  | [], D => D
  | g :: p, D => g.applyCode (run p D)

def word : GenerationProgram n → BinaryVector n → BinaryVector n
  | [], x => x
  | g :: p, x => g.applyWord (word p x)

@[simp] theorem run_nil (D : BinaryCode n) : run [] D = D := rfl
@[simp] theorem run_cons (g : GenerationGate n) (p : GenerationProgram n) (D : BinaryCode n) :
    run (g :: p) D = g.applyCode (run p D) := rfl

@[simp] theorem run_append (p q : GenerationProgram n) (D : BinaryCode n) :
    run (p ++ q) D = run p (run q D) := by
  induction p with
  | nil => rfl
  | cons g p ih => simp only [List.cons_append, run_cons, ih]

@[simp] theorem word_append (p q : GenerationProgram n) (x : BinaryVector n) :
    word (p ++ q) x = word p (word q x) := by
  induction p with
  | nil => rfl
  | cons g p ih => simp only [List.cons_append, word, ih]

def inverse (p : GenerationProgram n) : GenerationProgram n := (p.map GenerationGate.inverse).reverse

@[simp] theorem inverse_nil : inverse ([] : GenerationProgram n) = [] := rfl
@[simp] theorem inverse_cons (g : GenerationGate n) (p : GenerationProgram n) :
    inverse (g :: p) = inverse p ++ [g.inverse] := by simp [inverse]

@[simp] theorem inverse_length (p : GenerationProgram n) : p.inverse.length = p.length := by
  simp [inverse]

theorem run_inverse (p : GenerationProgram n) (D : BinaryCode n) :
    run p.inverse (run p D) = D := by
  induction p with
  | nil => rfl
  | cons g p ih =>
    rw [inverse_cons, run_append, run_cons, run_cons, run_nil,
      GenerationGate.applyCode_inverse, ih]

theorem word_inverse (p : GenerationProgram n) (x : BinaryVector n) :
    word p.inverse (word p x) = x := by
  induction p with
  | nil => rfl
  | cons g p ih =>
    rw [inverse_cons, word_append]
    change word (inverse p) (g.inverse.applyWord (g.applyWord (word p x))) = x
    rw [GenerationGate.applyWord_inverse, ih]

@[simp] theorem inverse_inverse (p : GenerationProgram n) : p.inverse.inverse = p := by
  simp [inverse, List.map_reverse, List.map_map, Function.comp_def]

theorem word_bijective (p : GenerationProgram n) : Function.Bijective p.word := by
  constructor
  · exact Function.LeftInverse.injective (word_inverse p)
  · intro x
    refine ⟨word p.inverse x, ?_⟩
    simpa only [inverse_inverse] using word_inverse p.inverse x

theorem run_image (p : GenerationProgram n) (D : BinaryCode n) (x : BinaryVector n) :
    x ∈ p.run D ↔ ∃ y ∈ D, p.word y = x := by
  induction p generalizing x with
  | nil => simp [run, word]
  | cons g p ih =>
    rw [run_cons, GenerationGate.applyCode_image]
    simp only [ih]
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, hz⟩
      exact ⟨y, hy, hz⟩
    · rintro ⟨y, hy, hx⟩
      exact ⟨word p y, ⟨y, hy, rfl⟩, hx⟩

theorem preserves_selfDual (p : GenerationProgram n) (D : BinaryCode n) (hD : SelfDual D) :
    SelfDual (p.run D) := by
  induction p with
  | nil => exact hD
  | cons g p ih => exact g.preserves_selfDual _ ih

end GenerationProgram

end
end Holant.ReedMuller.FlatNetwork
